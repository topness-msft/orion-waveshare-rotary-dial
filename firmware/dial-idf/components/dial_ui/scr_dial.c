/*
 * SCR_DIAL — the temperature dial (design-spec.md §4, "HOME FACE").
 * Arc drag + knob detents set the target °F; tap the power disc to toggle;
 * swipe left/right to show the other side. All input posts commands to the
 * worker queue and renders optimistically; the poll reconciles later.
 *
 * The chassis ring (arc), fixed numeral anchor, and state-token colors are
 * shared vocabulary with scr_standby (same r=165 ring, same palette) — see
 * dial_palette.h and ui_screens_internal.h's dial_zone_kind/dial_zone_accent.
 */
#include "ui_screens_internal.h"
#include "dial_haptics.h"
#include "dial_ota.h"
#include "dial_icons.h"
#include <math.h>
#include <time.h>

LV_FONT_DECLARE(dial_font_num_88)

#define CX 180   // screen center — every position in design-spec.md §4 is
#define CY 180   // given as an absolute (x,y); we align everything to the
                 // screen's center and offset by (x-CX, y-CY).
#define ARC_R 165
#define RAIL_BOOST_MINUTES 30
#define RAIL_BOOST_SEQ_MS 1500

static lv_obj_t *s_arc;
static lv_obj_t *s_stale_dot;
static lv_obj_t *s_zero_notch;   // neutral (level 0) landmark, relative mode only
static lv_obj_t *s_handle;       // setpoint drag handle — the ONLY temp touch target

/*
 * Water level, drawn as a VALUE STEP rather than a texture: no stripes, no
 * second material — the arc says where the water is purely by changing the
 * value of what's already there. One overlay arc, two configurations, and the
 * boundary between them IS the water level:
 *
 *   HEATING  water below the setpoint, so the water sits UNDER the accent fill.
 *            That stretch of fill is deepened (a `bg` wash over it), leaving the
 *            rest of the fill bright: dark = water that's really there, bright =
 *            the heat still to add.
 *   COOLING  water above the setpoint, so it overshoots the fill. The overshoot
 *            is the accent at low opacity over the bare track: a ghost of the
 *            fill, which is exactly what it is — heat that has to leave.
 *
 * There is nothing to alias and nothing to animate, and the water never becomes
 * a third color to decode: it's the same accent, one step down in value.
 *
 * The under-fill stretch is not deepened when cooling — the water level there is
 * already above the setpoint by definition, so the only thing worth marking is
 * where it overshoots to.
 *
 * Recomputed only when a poll moves the water or the user moves the target.
 */
#define LEVEL_OPA_UNDER  77     // ~30%: `bg` wash deepening the fill  (heating)
#define LEVEL_OPA_OVER   82     // ~32%: accent ghost over the track   (cooling)

static lv_obj_t  *s_level;              // the value-step overlay arc
static lv_color_t s_level_accent;       // cached: the drag path has no state snapshot
static float      s_actual_f = -1.0f;   // measured water temp, °F; <0 = unknown

static lv_obj_t *s_name_lbl;
static lv_obj_t *s_underline_solid, *s_underline_dash;
static lv_obj_t *s_water_lbl;
static lv_obj_t *s_num_box, *s_temp_lbl;
static lv_obj_t *s_unit_lbl;
static lv_obj_t *s_pill, *s_pill_glyph, *s_pill_word, *s_pill_close;
static lv_obj_t *s_power_btn, *s_power_glyph;
// Boost glyphs capping the two ends of the arc (owner: relocate the boost
// controls off the dial face and onto "the end of the arc" itself — see the
// #3c block in create() for the geometry and the handle-precedence note).
// s_boost_cool_icon/s_boost_heat_icon are the glyphs only, purely visual;
// s_boost_cool_tap/s_boost_heat_tap are the real (invisible) touch targets,
// a separate object biased inward from the glyph.
static lv_obj_t *s_boost_cool_pad, *s_boost_heat_pad;
static lv_obj_t *s_boost_cool_icon, *s_boost_heat_icon;
static lv_obj_t *s_boost_cool_tap, *s_boost_heat_tap;
static lv_obj_t *s_dot_a, *s_dot_b, *s_dot_menu;
static lv_obj_t *s_away_lbl;
static lv_obj_t *s_ota_lbl;   // OTA notice, dual-purpose: "Finalizing
                               // update..." / "Update available" — see create()
static lv_point_t s_dash_pts[2];

static zone_idx_t s_zone = ZONE_A;

// The setpoint currently shown (optimistic); -1 until first state arrives.
static int s_shown_f = -1;

// Display-units cache (design-spec.md's units toggle, M4): updated from
// apply_palette_and_state on every on_state, read by render_numeral — which
// is also called mid-drag/mid-detent, where only the raw °F value is at
// hand. The store keeps the setpoint in °F regardless.
static bool s_units_c;

// Relative-scale cache (owner: togglable absolute/relative setpoint scale),
// same lifecycle as s_units_c: set from apply_palette_and_state, read by
// render_numeral and on_knob (both run without a fresh snapshot). The internal
// setpoint stays whole °F; relative is a −10…+10 level view over it.
static bool s_rel;

// Relief-active cache for the knob guard: a detent during a boost is inert
// (owner decision) so a stray turn can't silently rewrite the setpoint by up
// to 2.5°C while the pill still counts down. Set from apply_palette_and_state.
static bool s_relief_active;

// Current configured arc range (°F). Absolute mode keeps the shipped 55–110;
// relative mode widens to 50–113 so all 21 levels are reachable (owner: widen
// only in relative mode, so an existing °F user's arc never moves). -1 forces
// configure_arc_range() to set it on the first render after each create().
static int s_arc_min = -1, s_arc_max = -1;

// Setpoint drag handle state. s_dragging is true between the handle's PRESSED
// and RELEASED so on_gesture/on_state never fight an in-progress drag; s_press_f
// is the setpoint at press start, so a tap on the handle (no movement) commits
// nothing.
static bool s_dragging;
static int  s_press_f;

// Over-rotating past either temperature rail starts the matching boost. Keep
// the setpoint from the start of the railward spin so the required scroll to
// -10/+10 does not become the boost's return temperature.
static int     s_knob_seq_start_f = -1;
static int     s_knob_seq_dir;
static uint32_t s_knob_seq_ms;

// Chevron pulse (design-spec.md §6): only running while heating/cooling, and
// only restarted when that changes or the day/night duration changes.
static bool s_chevron_active;
static bool s_chevron_night;

// Only fade the staleness dot on an actual transition, not every on_state.
static bool s_stale_shown;

// Boost ("thermal relief") countdown: a 1s ticker that only exists while the
// shown zone's relief is active — created lazily on the transition into
// relief, deleted on the transition out (and on destroy()).
static lv_timer_t *s_boost_timer;

/* ---- motion helpers (design-spec.md §6) -------------------------------- */

static void set_zoom_cb(void *obj, int32_t v) { lv_obj_set_style_transform_zoom((lv_obj_t *)obj, (int16_t)v, 0); }
static void set_x_cb(void *obj, int32_t v)    { lv_obj_set_x((lv_obj_t *)obj, (lv_coord_t)v); }
static void set_opa_cb(void *obj, int32_t v)  { lv_obj_set_style_opa((lv_obj_t *)obj, (lv_opa_t)v, 0); }

// Detent zoom bump: 256->266->256 over 90ms on the numeral only.
static void anim_zoom_bump(lv_obj_t *obj)
{
    lv_anim_del(obj, set_zoom_cb);
    lv_obj_set_style_transform_zoom(obj, 256, 0);
    lv_anim_t a;
    lv_anim_init(&a);
    lv_anim_set_var(&a, obj);
    lv_anim_set_exec_cb(&a, set_zoom_cb);
    lv_anim_set_values(&a, 256, 266);
    lv_anim_set_time(&a, 45);
    lv_anim_set_playback_time(&a, 45);
    lv_anim_set_path_cb(&a, lv_anim_path_ease_out);
    lv_anim_start(&a);
}

// Range-stop nudge: instant 4px kick in the blocked direction, one-overshoot
// spring back over 140ms (numeral + indicator, design-spec.md §6).
static void anim_nudge(lv_obj_t *obj, int dir)
{
    lv_anim_del(obj, set_x_cb);
    lv_obj_set_x(obj, 4 * dir);
    lv_anim_t a;
    lv_anim_init(&a);
    lv_anim_set_var(&a, obj);
    lv_anim_set_exec_cb(&a, set_x_cb);
    lv_anim_set_values(&a, 4 * dir, 0);
    lv_anim_set_time(&a, 140);
    lv_anim_set_path_cb(&a, lv_anim_path_overshoot);
    lv_anim_start(&a);
}

// Generic opacity fade to an arbitrary target (the staleness dot's
// night-quiet level, M4) — like lv_obj_fade_in/out but not hardcoded to
// LV_OPA_COVER, reusing set_opa_cb above.
static void anim_opa(lv_obj_t *obj, lv_opa_t from, lv_opa_t to, uint32_t time_ms)
{
    lv_anim_del(obj, set_opa_cb);
    lv_anim_t a;
    lv_anim_init(&a);
    lv_anim_set_var(&a, obj);
    lv_anim_set_exec_cb(&a, set_opa_cb);
    lv_anim_set_values(&a, from, to);
    lv_anim_set_time(&a, time_ms);
    lv_anim_set_path_cb(&a, lv_anim_path_linear);
    lv_anim_start(&a);
}

// State chevron pulse: pill glyph opa 60%<->100%, 1.2s day / 2.4s night,
// ping-pong, infinite — only while heating/cooling (design-spec.md §6).
static void chevron_start(bool night)
{
    lv_anim_del(s_pill_glyph, set_opa_cb);
    uint32_t half = night ? 2400 : 1200;
    lv_anim_t a;
    lv_anim_init(&a);
    lv_anim_set_var(&a, s_pill_glyph);
    lv_anim_set_exec_cb(&a, set_opa_cb);
    lv_anim_set_values(&a, LV_OPA_60, LV_OPA_100);
    lv_anim_set_time(&a, half);
    lv_anim_set_playback_time(&a, half);
    lv_anim_set_repeat_count(&a, LV_ANIM_REPEAT_INFINITE);
    lv_anim_set_path_cb(&a, lv_anim_path_ease_in_out);
    lv_anim_start(&a);
}

static void chevron_stop(void)
{
    lv_anim_del(s_pill_glyph, set_opa_cb);
    lv_obj_set_style_opa(s_pill_glyph, LV_OPA_100, 0);
}

/* ---- water level: value step over the arc ------------------------------ */

// Temperature -> degrees into the arc's own 0..270 sweep (rotation adds 135).
// Same mapping the setpoint indicator uses, so the level and the fill land on
// one scale. Uses the CURRENT arc range so the water overlay stays aligned with
// the (mode-dependent) indicator — 55–110 in absolute, 50–113 in relative.
static uint16_t level_angle(float f)
{
    if (f < s_arc_min) f = s_arc_min;
    if (f > s_arc_max) f = s_arc_max;
    float d = 270.0f * (f - s_arc_min) / (float)(s_arc_max - s_arc_min);
    return (uint16_t)lroundf(d);
}

// Point the arc (and thus level_angle) at the range the current scale needs.
// Cheap and idempotent — only touches the widget when the range actually
// changes (a mode toggle OR a fresh device-reported range landing), so it
// never disturbs an in-progress drag. Absolute mode's rails come from the
// device itself (dial_state_temp_min_f/_max_f — owner: use Orion's own
// min/max, not a hardcoded guess), falling back to DIAL_TEMP_MIN_F/MAX_F
// only before discovery has run; relative mode's 21-level table is
// untouched by this and keeps its own fixed rails.
static void configure_arc_range(const app_state_t *st)
{
    int mn = s_rel ? DIAL_REL_MIN_F : dial_state_temp_min_f(st);
    int mx = s_rel ? DIAL_REL_MAX_F : dial_state_temp_max_f(st);
    if (mn != s_arc_min || mx != s_arc_max) {
        lv_arc_set_range(s_arc, mn, mx);
        s_arc_min = mn;
        s_arc_max = mx;
    }
}

/* ---- setpoint handle geometry ------------------------------------------ */
// The arc sweeps 270° starting at 135° (lower-left), clockwise over the top to
// 45° (lower-right); the remaining 90° at the bottom is the gap. Both helpers
// share that mapping so the handle rides exactly on the fill's leading edge.

// Place the handle centered ON the arc band (not on its outer edge). LVGL draws
// its own knob at the band centerline = (inner span)/2 − indic_width/2; we mirror
// that exactly, read from the live object, so the handle sits dead-center on the
// ring regardless of the arc's padding.
static void position_handle(int f)
{
    if (!s_handle || s_arc_max <= s_arc_min) return;
    lv_coord_t span = LV_MIN(lv_obj_get_width(s_arc), lv_obj_get_height(s_arc))
                      - lv_obj_get_style_pad_left(s_arc, LV_PART_MAIN)
                      - lv_obj_get_style_pad_right(s_arc, LV_PART_MAIN);
    float r = (span > 0 ? span : 2 * ARC_R) / 2.0f
              - lv_obj_get_style_arc_width(s_arc, LV_PART_INDICATOR) / 2.0f;
    float frac = (float)(f - s_arc_min) / (float)(s_arc_max - s_arc_min);
    if (frac < 0.0f) frac = 0.0f;
    if (frac > 1.0f) frac = 1.0f;
    float ang = (135.0f + frac * 270.0f) * (float)M_PI / 180.0f;
    int dx = (int)lroundf(r * cosf(ang));
    int dy = (int)lroundf(r * sinf(ang));
    lv_obj_align(s_handle, LV_ALIGN_CENTER, dx, dy);
}

// Map a live touch point (screen coords) back to a setpoint °F along the sweep.
// Angles in the bottom gap fold to whichever rail is nearer, so a finger that
// slides off the bottom pins cleanly instead of jumping across the gap.
static int value_from_point(lv_point_t p)
{
    float theta = atan2f((float)(p.y - CY), (float)(p.x - CX)) * 180.0f / (float)M_PI;
    if (theta < 0.0f) theta += 360.0f;              // 0..360, 0 at 3 o'clock, +cw
    float sweep = theta - 135.0f;                   // 0 at the arc's start
    if (sweep < 0.0f) sweep += 360.0f;
    if (sweep > 270.0f) sweep = (sweep > 315.0f) ? 0.0f : 270.0f;   // gap -> nearer rail
    float frac = sweep / 270.0f;
    return s_arc_min + (int)lroundf(frac * (float)(s_arc_max - s_arc_min));
}

static void level_render(int target_f)
{
    if (!s_level) return;
    if (s_actual_f < 0) {                       // no measurement yet
        lv_obj_add_flag(s_level, LV_OBJ_FLAG_HIDDEN);
        return;
    }

    uint16_t a_water = level_angle(s_actual_f);
    uint16_t a_set   = level_angle((float)target_f);
    bool cooling = a_water > a_set;

    uint16_t a0 = cooling ? a_set : 0;
    uint16_t a1 = a_water;
    if (a1 <= a0 + 1) {                         // at target: no step to draw
        lv_obj_add_flag(s_level, LV_OBJ_FLAG_HIDDEN);
        return;
    }

    lv_obj_set_style_arc_color(s_level, cooling ? s_level_accent : PAL()->bg, LV_PART_INDICATOR);
    lv_obj_set_style_arc_opa(s_level, cooling ? LEVEL_OPA_OVER : LEVEL_OPA_UNDER, LV_PART_INDICATOR);
    lv_arc_set_angles(s_level, a0, a1);
    lv_obj_clear_flag(s_level, LV_OBJ_FLAG_HIDDEN);
}

/* ---- identity underline (design-spec.md §4 #6, §8) --------------------- */
// ZONE_A is "yours" (always solid); ZONE_B is the partner (solid pewter by
// day, dashed warm-hue by night — the hue->pattern substitution rule).
static void apply_identity(const dial_palette_t *pal, bool night)
{
    if (s_zone == ZONE_A) {
        lv_obj_set_style_bg_color(s_underline_solid, pal->identity_home, 0);
        lv_obj_clear_flag(s_underline_solid, LV_OBJ_FLAG_HIDDEN);
        lv_obj_add_flag(s_underline_dash, LV_OBJ_FLAG_HIDDEN);
    } else if (night) {
        lv_obj_set_style_line_color(s_underline_dash, pal->identity_partner, 0);
        lv_obj_clear_flag(s_underline_dash, LV_OBJ_FLAG_HIDDEN);
        lv_obj_add_flag(s_underline_solid, LV_OBJ_FLAG_HIDDEN);
    } else {
        lv_obj_set_style_bg_color(s_underline_solid, pal->identity_partner, 0);
        lv_obj_clear_flag(s_underline_solid, LV_OBJ_FLAG_HIDDEN);
        lv_obj_add_flag(s_underline_dash, LV_OBJ_FLAG_HIDDEN);
    }
}

// "Until H:MM" — 12h, no AM/PM, ASCII, same format scr_standby.c's clock
// uses — shared by every pill state below that shows a future clock time.
static void format_until(int minutes_from_midnight, char *out, size_t outsz)
{
    int h12 = (minutes_from_midnight / 60) % 12;
    if (h12 == 0) h12 = 12;
    snprintf(out, outsz, "Until %d:%02d", h12, minutes_from_midnight % 60);
}

/* ---- palette + state application --------------------------------------- */
// Re-applied from on_state every render (cheap): both device telemetry and a
// palette swap (day/night) land here, so neither needs its own code path.
static void apply_palette_and_state(const app_state_t *st)
{
    const dial_palette_t *pal = PAL();
    bool night = dial_palette_is_night();
    s_units_c = st->units_c;
    s_rel     = st->rel_mode;
    configure_arc_range(st);     // point the arc at this scale's rails
    const zone_state_t *z = &st->zones[s_zone];
    zone_kind_t kind = dial_zone_kind(z, st->device_online);
    lv_color_t accent = dial_zone_accent(kind, pal);

    // Thermal relief ("boost") in progress: the arc + pill switch to the
    // relief's own heat/cool accent and go full-strength, regardless of what
    // kind/opacity the ordinary state grammar would otherwise pick — the
    // power disc below stays kind-based (boost doesn't change on/off meaning).
    bool relief = z->relief_active;
    s_relief_active = relief;    // knob guard reads this without a fresh snapshot
    lv_color_t relief_accent = z->relief_heat ? pal->accent_heat : pal->accent_cool;
    lv_color_t arc_accent = relief ? relief_accent : accent;

    lv_obj_t *scr = lv_obj_get_parent(s_arc);   // s_arc's parent is the screen
    lv_obj_set_style_bg_color(scr, pal->bg, 0);

    // Arc track + indicator (design-spec.md §4 #2-3).
    lv_obj_set_style_arc_color(s_arc, pal->track, LV_PART_MAIN);
    lv_obj_set_style_arc_opa(s_arc, LV_OPA_70, LV_PART_MAIN);
    lv_obj_set_style_arc_color(s_arc, arc_accent, LV_PART_INDICATOR);
    lv_opa_t indic_opa = relief ? LV_OPA_COVER
                        : (kind == ZK_OFFLINE) ? LV_OPA_TRANSP
                        : (kind == ZK_STANDBY) ? LV_OPA_30 : LV_OPA_COVER;
    lv_obj_set_style_arc_opa(s_arc, indic_opa, LV_PART_INDICATOR);

    // Water level. Cached in °F (and the accent with it) so a drag or a detent
    // can re-draw the step without waiting for the next poll — the water doesn't
    // move while you turn the knob, but the setpoint does, and that's what
    // decides which side of it the water is on.
    s_actual_f = (z->actual_c >= 0) ? (float)dial_c_to_f(z->actual_c) : -1.0f;
    s_level_accent = arc_accent;
    level_render(s_shown_f);

    // Side name + identity underline.
    lv_obj_set_style_text_color(s_name_lbl, pal->ink_secondary, 0);
    apply_identity(pal, night);

    // Water caption — display-only °C conversion when units_c (M4); the
    // store keeps actual_c as-is either way.
    lv_obj_set_style_text_color(s_water_lbl, pal->ink_secondary, 0);
    lv_obj_set_style_text_opa(s_water_lbl, LV_OPA_80, 0);
    char water[16];
    if (z->actual_c < 0) snprintf(water, sizeof(water), "WATER --");
    else if (st->units_c) snprintf(water, sizeof(water), "WATER %.1f\xC2\xB0", z->actual_c);
    else snprintf(water, sizeof(water), "WATER %d\xC2\xB0", dial_c_to_f(z->actual_c));
    lv_label_set_text(s_water_lbl, water);

    // Setpoint numeral — ink_primary always (never state-tinted); dimmed only
    // for OFFLINE (design-spec.md's "numeral whose color never lies").
    lv_obj_set_style_text_color(s_temp_lbl, pal->ink_primary, 0);
    lv_obj_set_style_text_opa(s_temp_lbl, (kind == ZK_OFFLINE) ? 115 : LV_OPA_COVER, 0);
    lv_obj_set_style_text_color(s_unit_lbl, pal->ink_secondary, 0);
    // Relative mode has no unit — the suffix names the quantity instead (mirrors
    // scr_boost's "MIN"). The measured-water caption above keeps its degree, so
    // an absolute reference stays on the face in every mode.
    if (st->rel_mode) lv_label_set_text(s_unit_lbl, "LEVEL");
    else              lv_label_set_text(s_unit_lbl, st->units_c ? "\xC2\xB0" "C" : "\xC2\xB0" "F");

    // Neutral landmark: a tick at 12 o'clock (level 0's center) shown only in
    // relative mode — it turns the ring from a plain bar into a bipolar
    // instrument. Geometrically free: the arc's midpoint already sits at top.
    lv_obj_set_style_bg_color(s_zero_notch, pal->ink_secondary, 0);
    if (s_rel) lv_obj_clear_flag(s_zero_notch, LV_OBJ_FLAG_HIDDEN);
    else       lv_obj_add_flag(s_zero_notch, LV_OBJ_FLAG_HIDDEN);

    // Setpoint handle: themed to the live accent and parked at the setpoint.
    // Left alone while the user is dragging it — they own s_shown_f then, and a
    // reposition from a stray commit would fight the finger.
    lv_obj_set_style_bg_color(s_handle, arc_accent, 0);
    if (!s_dragging) position_handle(s_shown_f);

    // State pill: surface fill, state-accent border/text/glyph. While relief
    // is active it takes over the pill entirely (glyph + countdown word +
    // a trailing close mark), pre-empting the ecobee-style hold/until
    // grammar below (§3 rework).
    lv_obj_set_style_bg_color(s_pill, pal->surface, 0);
    lv_obj_set_style_border_color(s_pill, relief ? relief_accent : accent, 0);
    lv_obj_set_style_text_color(s_pill_glyph, relief ? relief_accent : accent, 0);
    lv_obj_set_style_text_color(s_pill_word, relief ? relief_accent : accent, 0);
    // Leading glyph's font switches with it: dial_font_icons_16 — the SAME
    // face the boost icons (§3c's arc-end glyphs) now use, sized to sit
    // level with this pill's Mont16 text — see dial_icons.h; the non-relief
    // glyphs below are stock LV_SYMBOL_* form, which only the Montserrat
    // font faces carry.
    lv_obj_set_style_text_font(s_pill_glyph, relief ? &dial_font_icons_16 : &lv_font_montserrat_16, 0);
    const char *glyph;
    char word[24];
    if (relief) {
        // Same glyph choice as the dial-face boost icons (§3c) — flame/
        // snow3, colored with that icon's own accent (relief_accent
        // above already is accent_heat/accent_cool by z->relief_heat) — so
        // the chip visually matches whichever icon started this boost.
        glyph = z->relief_heat ? DIAL_ICON_FLAME : DIAL_ICON_SNOW3;
        // "Until H:MM" rather than a ticking countdown (owner request): the
        // end time is the fact worth knowing, it matches every other state
        // this chip shows, and it doesn't force a re-render every second.
        // Falls back to the bare word when the clock isn't usable, since
        // without it there is no honest time to print.
        time_t   end_s = (time_t)(z->relief_end_ms / 1000);
        struct tm end_lt;
        if (st->clock_valid && z->relief_end_ms > 0 && localtime_r(&end_s, &end_lt))
            format_until(end_lt.tm_hour * 60 + end_lt.tm_min, word, sizeof(word));
        else
            snprintf(word, sizeof(word), "BOOST");
    } else {
        // §3: the pill's permanent, non-relief job is now "will this setpoint
        // hold, or expire" — not restating HEATING/COOLING/OFFLINE/STANDBY,
        // which the arc's accent + chevron pulse and the staleness dot
        // already carry (ZK_OFFLINE IS !device_online, exactly the staleness
        // dot's own condition — nothing unique is lost dropping the word).
        //
        // Priority (owner refinement): an OFF zone with a bedtime still
        // ahead today isn't "holding" — nothing is being held, the schedule
        // is going to switch it ON — so that gets its own case, checked
        // BEFORE hold_until_min (which only describes the WRITE path for a
        // zone that's already on). "Still ahead" needs its own clock read
        // (hold_until_min doesn't cover the off case at all — it's scoped
        // to write-path behavior, see dial_state.h's comment on the field),
        // done here with the same clock-validity discipline the relief
        // countdown above uses: raw time(NULL) gated on st->clock_valid,
        // not dial_time_now() (that function is worker-only) — this mirrors
        // the store's own mirror of clock validity rather than adding a new
        // dial_ui -> dial_time dependency for a one-line comparison.
        int bed_min;
        bool off_bedtime_ahead = false;
        if (!z->on && z->sched_valid && st->clock_valid &&
            dial_parse_hhmm(z->sched_bedtime, &bed_min)) {
            time_t now = time(NULL);
            struct tm lt;
            localtime_r(&now, &lt);
            int now_min = lt.tm_hour * 60 + lt.tm_min;
            off_bedtime_ahead = now_min < bed_min;   // else falls through — bedtime already passed today
        }

        if (off_bedtime_ahead) {
            glyph = LV_SYMBOL_PAUSE;   // paused, not holding — the schedule turns it on
            format_until(bed_min, word, sizeof(word));
        } else if (z->hold_until_min < 0) {
            // z->hold_until_min is the WORKER's answer (main.c's
            // compute_hold_until_min, refreshed every idle tick — see
            // dial_state.h's comment on the field) so this half is pure
            // render, no schedule math here.
            glyph = LV_SYMBOL_PAUSE;
            strlcpy(word, "Holding", sizeof(word));
        } else {
            glyph = LV_SYMBOL_LOOP;   // "reverts to the schedule" — no clock glyph in this font
            format_until(z->hold_until_min, word, sizeof(word));
        }
    }
    lv_label_set_text(s_pill_glyph, glyph);
    lv_label_set_text(s_pill_word, word);

    // Trailing close mark: a visual affordance only (the tap target is the
    // WHOLE chip — see the CLICKABLE toggle right below), stock
    // LV_SYMBOL_CLOSE (needs no new asset), same accent as the rest of the
    // chip. Hidden outside relief — there's nothing to close then.
    lv_obj_set_style_text_color(s_pill_close, relief_accent, 0);
    if (relief) lv_obj_clear_flag(s_pill_close, LV_OBJ_FLAG_HIDDEN);
    else        lv_obj_add_flag(s_pill_close, LV_OBJ_FLAG_HIDDEN);

    // The chip has exactly two modes (owner correction — the Holding/Until
    // tap-to-SCR_ADJUST_MODE hand-off from an earlier pass is GONE; that
    // screen is reached only from Settings and the power-disc long-press
    // now): relief active -> the whole chip is one cancel target;
    // otherwise -> not interactive at all, CLICKABLE cleared so a tap falls
    // through to whatever's underneath instead of doing something
    // surprising. ext_click_area only while clickable, so Holding/Until
    // never claims a bigger invisible hit box than what's actually tappable.
    // Capped at 4px (not this project's usual 14): the pill sits only 5px
    // below the setpoint numeral's own box (s_num_box, #8, bottom edge
    // absolute y=196 vs the pill's top edge y=201) — any more padding here
    // starts stealing taps off the numeral's dead zone above. Downward there
    // is much more room (17px to the power disc's now-72px-diameter top
    // edge), but ext_click_area is uniform on all sides in LVGL 8.4, so the
    // tighter side sets the number for both.
    if (relief) {
        lv_obj_add_flag(s_pill, LV_OBJ_FLAG_CLICKABLE);
        lv_obj_set_ext_click_area(s_pill, 4);
    } else {
        lv_obj_clear_flag(s_pill, LV_OBJ_FLAG_CLICKABLE);
        lv_obj_set_ext_click_area(s_pill, 0);
    }

    // Chevron pulse tracks the underlying thermal kind, not relief — a boost
    // still pulses (on the charge glyph) while the zone is actively driving
    // toward the relief extreme, and goes static once it's holding there.
    bool pulsing = (kind == ZK_HEATING || kind == ZK_COOLING);
    if (pulsing && (!s_chevron_active || night != s_chevron_night)) chevron_start(night);
    else if (!pulsing && s_chevron_active) chevron_stop();
    s_chevron_active = pulsing;
    s_chevron_night = night;

    // Power button — the PRIMARY control on this face — always carries a
    // clearly visible border (owner correction: it used to go to pal->track
    // when off, which reads as near-invisible against the background, while
    // the secondary boost buttons below kept a full ring at rest — exactly
    // backwards). Off: ink_secondary (visible, but quieter than the on
    // state's accent). On: accent, unchanged.
    lv_obj_set_style_bg_color(s_power_btn, pal->surface, 0);
    lv_obj_set_style_border_color(s_power_btn, z->on ? accent : pal->ink_secondary, 0);
    lv_obj_set_style_text_color(s_power_glyph, z->on ? pal->ink_primary : pal->ink_secondary, 0);

    // Boost glyphs capping the arc ends (§3c) — SECONDARY controls, so they
    // must read quieter than the power button, not louder: no chrome at all
    // (no fill, no border — they're just glyphs sitting on the ring, not
    // buttons). Colour (owner, after seeing ink_secondary on hardware: "too
    // prominent... make them blend in with the arc colour palette, making it
    // look like the arc"): each glyph is its OWN direction's accent
    // (accent_cool/accent_heat — the same hue the arc fill uses at that end),
    // opacity-muted rather than recoloured so it still blends with whatever
    // is actually drawn underneath it (the arc's own track or fill pixels).
    // Two candidate rest treatments were rendered and compared pixel-by-pixel
    // before picking this one:
    //   - pal->track (max "looks like the arc"): rejected — against the
    //     rendered PNGs the glyphs were essentially invisible everywhere
    //     except squarely over bare background; over the arc's own track or
    //     fill (i.e. most of the time, since they sit ON the ring) they
    //     vanished completely, worst at night where track/bg are already
    //     both dim.
    //   - accent_cool/accent_heat, opacity-muted (this one): keeps the hue
    //     relationship the arc already encodes (cool end / hot end) while
    //     dropping the brightness that made ink_secondary pop as a separate
    //     object.
    //
    // Three tiers per glyph, not two (owner, second pass: "no muted variant
    // for when the pad is off" — a single LV_OPA_60-on-accent rest state was
    // the liveliest thing on a screen that's supposed to look dormant once
    // z->on is false, since the arc drops to neutral_standby and the pill
    // greys out the same way):
    //   1. THAT direction's relief running -> its own accent, LV_OPA_COVER.
    //      Unchanged — still the brightest thing here, on purpose.
    //   2. Zone on, nothing running -> its own accent, LV_OPA_60. Unchanged
    //      from the first pass; measured legible in every case checked (day
    //      with the fill passing under it, day over bare track, the night
    //      palette) — peak ink channel sum stayed >=150 against a <=100
    //      background in all of them.
    //   3. Zone off -> pal->neutral_standby (not the direction's accent —
    //      there's no "which direction" to hint at when the pad is off) at
    //      LV_OPA_30. Both numbers are lifted directly from how the rest of
    //      this off face already renders: the arc's own indicator uses
    //      exactly neutral_standby at exactly LV_OPA_30 for kind==ZK_STANDBY
    //      (see indic_opa above), so the glyph now fades to the SAME colour
    //      and SAME intensity as the ring it sits on, rather than inventing
    //      a fourth "off" look. At night this is the dimmest combination on
    //      the device (neutral_standby's night value is already close to
    //      the night bg, and these sit near the rim where the panel's own
    //      glow is weakest) — checked on a rendered night+off frame; the
    //      glyphs are barely there, which reads as correct for a dormant
    //      bedside device at 3am rather than a bug (see the report).
    // Full-strength on relief still roughly triples the on-rest peak
    // (measured ~90->239 on the red channel for heat) and is drastically
    // brighter than the off-rest tier, so lighting up reads as an obvious
    // state change against either muted rest look, never an ambiguous one.
    // Boost-icon colour follows what the BED is doing, not what the boost
    // buttons are (owner, 2026-08-04): zone off -> both neutral; zone on and
    // actively heating -> flame keeps its accent while the snowflake stays
    // neutral, and vice versa for cooling. A running relief is subsumed by
    // this, since a relief always drives the zone into heating or cooling
    // anyway -- one rule instead of two that could disagree on screen.
    //
    // The neutral is neutral_standby (0x585858 by day) rather than
    // ink_secondary: ink is the TEXT tone and read as glaringly bright out on
    // the ring when it was tried there. Opacity still steps down when the
    // zone is off, since everything else on this face quiets then too.
    bool heating = !strcmp(z->thermal_state, "heating");
    bool cooling = !strcmp(z->thermal_state, "cooling");
    lv_color_t cool_rest_color = (z->on && cooling) ? pal->accent_cool : pal->neutral_standby;
    lv_color_t heat_rest_color = (z->on && heating) ? pal->accent_heat : pal->neutral_standby;
    lv_opa_t   cool_rest_opa   = z->on ? LV_OPA_70 : LV_OPA_40 + 13;   // ~45% when off
    lv_opa_t   heat_rest_opa   = cool_rest_opa;
    // Bead body + rim. The fill is `surface` (the same body the power button
    // and status chip use) so the icon reads as hardware ON the ring rather
    // than a hole through it; the rim follows the same active rule as the
    // glyph it frames. These lines were lost in an earlier edit and the beads
    // rendered with LVGL's default white — visible immediately in the render.
    lv_obj_set_style_bg_color(s_boost_cool_pad, pal->surface, 0);
    lv_obj_set_style_border_color(s_boost_cool_pad, (z->on && cooling) ? pal->accent_cool : pal->track, 0);
    lv_obj_set_style_bg_color(s_boost_heat_pad, pal->surface, 0);
    lv_obj_set_style_border_color(s_boost_heat_pad, (z->on && heating) ? pal->accent_heat : pal->track, 0);

    lv_obj_set_style_text_color(s_boost_cool_icon, cool_rest_color, 0);
    lv_obj_set_style_text_opa(s_boost_cool_icon, (z->on && cooling) ? LV_OPA_COVER : cool_rest_opa, 0);
    lv_obj_set_style_text_color(s_boost_heat_icon, heat_rest_color, 0);
    lv_obj_set_style_text_opa(s_boost_heat_icon, (z->on && heating) ? LV_OPA_COVER : heat_rest_opa, 0);

    // Staleness dot. Night-quiet errors (design-spec.md's "silent staleness
    // at night"): shown at 40% instead of full opacity after dark, so a
    // routine offline blip doesn't glow at 3am.
    lv_obj_set_style_bg_color(s_stale_dot, pal->stale, 0);
    lv_opa_t stale_target = night ? LV_OPA_40 : LV_OPA_COVER;
    bool stale = (st->phase != PH_READY) || !st->device_online;
    if (stale != s_stale_shown) {
        s_stale_shown = stale;
        if (stale) anim_opa(s_stale_dot, LV_OPA_TRANSP, stale_target, 300);
        else       anim_opa(s_stale_dot, lv_obj_get_style_opa(s_stale_dot, 0), LV_OPA_TRANSP, 300);
    } else if (stale) {
        // Still stale, no transition this render — keep the level in sync
        // with a day/night flip (e.g. the worker's dusk palette swap) even
        // without a fresh fade.
        lv_anim_del(s_stale_dot, set_opa_cb);
        lv_obj_set_style_opa(s_stale_dot, stale_target, 0);
    }

    // Page dots — one per face, in the order the chain walks them (see
    // on_gesture): Dial(B) - Dial(A) - Menu on a dual topper, and just
    // Dial - Menu on a single-zone one, re-centered so the pair sits
    // symmetric. Filled = the face this screen instance is showing; scr_dial
    // is never the menu face, so that dot always tracks.
    dial_dots_layout(st, s_dot_b, s_dot_a, s_dot_menu);
    lv_obj_set_style_bg_color(s_dot_b, s_zone == ZONE_B ? pal->ink_secondary : pal->track, 0);
    lv_obj_set_style_bg_color(s_dot_a, s_zone == ZONE_A ? pal->ink_secondary : pal->track, 0);
    lv_obj_set_style_bg_color(s_dot_menu, pal->track, 0);

    // Away badge (design-spec.md §7 extension) — session-optimistic, tiny.
    lv_obj_set_style_text_color(s_away_lbl, pal->ink_secondary, 0);
    if (st->away) lv_obj_clear_flag(s_away_lbl, LV_OBJ_FLAG_HIDDEN);
    else          lv_obj_add_flag(s_away_lbl, LV_OBJ_FLAG_HIDDEN);

    // OTA notice — one shared label, two mutually-exclusive states (see
    // create() for why both live in this exact slot):
    //   pending_verify (OTA rollback fix, M6) — "Finalizing update...".
    //     Mirrors dial_ota_info_t.pending_verify via main.c's mut_ota(), so
    //     it clears the moment ota_confirm_once() (first poll, or the 30s
    //     fallback timer) actually confirms the image. Not tappable —
    //     nothing to do about it but wait.
    //   OTA_AVAILABLE, not pending_verify, not night — "Update available".
    //     Passive ambient indicator (owner reassessment,
    //     docs/SPEC-update-prompt.md): unconditional on status + night, no
    //     idle window, no daily ceiling, no skip/defer interaction — those
    //     govern the SCR_UPDATE_PROMPT sheet, not this; a user who deferred
    //     the sheet still benefits from knowing. Tappable -> SCR_UPDATE.
    // pending_verify wins the shared slot on the rare tick both are true at
    // once (a fresh-boot confirm race with a newer release already
    // published — needs a manual "Check for updates" tap inside the ~30s
    // confirm window to even reach; the ~24h-uptime auto-checker in main.c
    // can't land there) — it's the more time-critical of the two.
    lv_obj_set_style_text_color(s_ota_lbl, pal->ink_secondary, 0);
    bool ota_finalizing = st->ota.pending_verify;
    bool ota_avail_notice = !ota_finalizing &&
                             (dial_ota_status_t)st->ota.status == OTA_AVAILABLE && !night;
    if (ota_finalizing) {
        lv_label_set_text(s_ota_lbl, "Finalizing update...");
        lv_obj_clear_flag(s_ota_lbl, LV_OBJ_FLAG_CLICKABLE);
        lv_obj_clear_flag(s_ota_lbl, LV_OBJ_FLAG_HIDDEN);
    } else if (ota_avail_notice) {
        lv_label_set_text(s_ota_lbl, "Update available");
        lv_obj_add_flag(s_ota_lbl, LV_OBJ_FLAG_CLICKABLE);
        lv_obj_clear_flag(s_ota_lbl, LV_OBJ_FLAG_HIDDEN);
    } else {
        lv_obj_clear_flag(s_ota_lbl, LV_OBJ_FLAG_CLICKABLE);
        lv_obj_add_flag(s_ota_lbl, LV_OBJ_FLAG_HIDDEN);
    }
}

// The value passed in is always °F — the internal representation. Relative mode
// shows the nearest −10…+10 level ("+3" / "0" / "-3"); the '+' is the glyph
// spliced into dial_font_num_88 (level 0 is a bare "0", no sign). Absolute mode
// keeps °F, or a one-decimal °C conversion when s_units_c (M4).
static void render_numeral(int temp_f)
{
    char t[8];
    if (s_rel) {
        int lvl = dial_rel_from_f(temp_f);
        if (lvl == 0) snprintf(t, sizeof(t), "0");
        else          snprintf(t, sizeof(t), "%+d", lvl);   // "+3" / "-3"
    } else if (s_units_c) {
        snprintf(t, sizeof(t), "%.1f", dial_f_to_c(temp_f));
    } else {
        snprintf(t, sizeof(t), "%d", temp_f);
    }
    lv_label_set_text(s_temp_lbl, t);
}

static void post_temp_for(zone_idx_t zone, int temp_f)
{
    if (zone == s_zone) s_shown_f = temp_f;
    dial_state_set_ui_temp(zone, temp_f);
    app_cmd_t cmd = { .kind = CMD_SET_TEMP, .zone = zone, .temp_f = temp_f };
    dial_cmd_post(&cmd);
}

static void post_temp(int temp_f) { post_temp_for(s_zone, temp_f); }

// Setpoint handle drag. The handle is the ONLY temperature touch target: the
// arc itself is display-only (non-clickable), so a press on the ring away from
// the handle — or anywhere in the centre — falls through to the screen and can
// become a page swipe. The handle does NOT bubble gestures, so a flick that
// begins on it adjusts temperature and never navigates. Between the two,
// swiping and temperature-setting are mutually exclusive by where the touch
// starts, which is exactly the behaviour the ring's whole-widget drag broke.
//
// LVGL keeps the press bound to the handle for the whole drag even as the finger
// travels off it around the ring, so PRESSING gives us the live point to map.
// The zone rides in user_data, bound at create() (see the note on power_event_cb).
static void handle_event_cb(lv_event_t *e)
{
    lv_event_code_t code = lv_event_get_code(e);
    zone_idx_t zone = (zone_idx_t)(uintptr_t)lv_event_get_user_data(e);

    if (code == LV_EVENT_PRESSED) {
        if (s_relief_active) return;      // handle is inert during a boost, like the knob
        s_knob_seq_start_f = -1;
        s_knob_seq_dir = 0;
        s_dragging = true;
        s_press_f = s_shown_f;
        dial_state_stamp_input();
        return;
    }
    if (!s_dragging) return;              // a press that didn't start a drag (relief)

    if (code == LV_EVENT_PRESSING) {
        lv_indev_t *indev = lv_indev_get_act();
        if (!indev) return;
        lv_point_t p;
        lv_indev_get_point(indev, &p);
        int f = value_from_point(p);
        // Live feedback: the fill, numeral (nearest level in relative), water
        // step and handle all follow the finger; nothing is committed until
        // release (matches the old arc-drag behaviour).
        s_shown_f = f;
        lv_arc_set_value(s_arc, f);
        render_numeral(f);
        level_render(f);
        position_handle(f);
        dial_state_stamp_input();
        return;
    }

    // LV_EVENT_RELEASED / LV_EVENT_PRESS_LOST — end of the drag.
    s_dragging = false;
    int f = s_shown_f;
    if (s_rel) {                          // commit exactly on Orion's level grid
        f = dial_rel_to_f(dial_rel_from_f(f));
        s_shown_f = f;
        lv_arc_set_value(s_arc, f);
        render_numeral(f);
        level_render(f);
        position_handle(f);
    }
    if (f != s_press_f) post_temp_for(zone, f);   // a tap that didn't move commits nothing
}

// Tap the ambient "Update available" notice (only clickable while it's
// showing that text — see apply_palette_and_state) — a light hand-off to
// SCR_UPDATE, same weight/haptic as scr_update_prompt.c's own "Update
// options" row. Never armed while it reads "Finalizing update...".
static void ota_notice_cb(lv_event_t *e)
{
    (void)e;
    dial_haptics_play(HAPTIC_TICK);
    ui_router_go(SCR_UPDATE, NULL, LV_SCR_LOAD_ANIM_NONE);
}

static void power_event_cb(lv_event_t *e)
{
    dial_state_stamp_input();
    dial_haptics_play(HAPTIC_CONFIRM);
    zone_idx_t zone = (zone_idx_t)(uintptr_t)lv_event_get_user_data(e);

    // Flip it in the store NOW, and tell the worker what we want rather than
    // asking it to toggle: the worker commits only after the write to Orion
    // returns, so deriving the new value there meant the face didn't move until
    // a TLS round trip had completed — a button that visibly did nothing for a
    // second. The next poll reconciles, and reverts this if the write failed.
    app_state_t st;
    dial_state_get(&st);
    bool want_on = !st.zones[zone].on;
    dial_state_set_zone_on(zone, want_on);

    app_cmd_t cmd = { .kind = CMD_TOGGLE_ON, .zone = zone, .a = want_on ? 1 : 0 };
    dial_cmd_post(&cmd);
}

// Tap the state pill: cancels the boost early. This is now the chip's ONLY
// job (owner correction: an earlier pass also opened SCR_ADJUST_MODE from
// here when not in relief — dropped; that screen is reached only from
// Settings and the power-disc long-press now, see power_long_press_cb). The
// event is only even reachable while relief is active — apply_palette_and_
// state clears CLICKABLE entirely otherwise (see that render's own comment)
// — but this still checks s_relief_active as a stale-tap guard: LVGL
// resolves a press's target at PRESS time, so a relief that ends between
// press and release could otherwise let a just-stale CLICKED through.
static void pill_event_cb(lv_event_t *e)
{
    (void)e;
    if (!s_relief_active) return;
    dial_haptics_play(HAPTIC_CONFIRM);
    // Optimistic FIRST, from this task: the worker commits too, but it may be
    // mid-poll and the queued command would then land seconds later.
    dial_state_set_relief_optimistic(-1, false, false, 0);   // device-wide, like the call itself
    app_cmd_t cmd = { .kind = CMD_BOOST_CANCEL };
    dial_cmd_post(&cmd);
}

// Long-press the POWER DISC (§2 — quick-actions' screen-wide long-press is
// gone; the boost controls and this replace what it carried) opens the
// Schedule/Hold picker (SCR_ADJUST_MODE) — the same destination temp_write_
// phase()'s comment in main.c ties directly to the knob's write behavior.
//
// A short tap on this same object still just toggles power (power_event_cb,
// LV_EVENT_CLICKED) — LVGL 8.4 fires CLICKED on release regardless of
// whether a LONG_PRESSED already fired for that press (verified by reading
// lv_indev.c's indev_proc_release: it sends CLICKED unconditionally whenever
// the touch didn't scroll, long-press or not), so without a guard a long
// press here would open the picker AND toggle the bed on release.
// lv_indev_wait_release() is this file's existing fix for exactly that
// shape — screen_long_press_cb used it the same way before quick-actions
// moved here: it makes LVGL swallow the rest of this touch (a harmless
// PRESS_LOST, no CLICKED) until the finger actually lifts.
//
// Packs `1 + s_zone` as SCR_ADJUST_MODE's origin arg (see that file's
// header comment for the full encoding) so its Back/swipe-right returns to
// THIS face/zone instead of hardcoding SCR_SETTINGS — this is one of that
// screen's three entry points.
static void power_long_press_cb(lv_event_t *e)
{
    (void)e;
    dial_state_stamp_input();
    dial_haptics_play(HAPTIC_TICK);
    lv_indev_wait_release(lv_indev_get_act());
    ui_router_go(SCR_ADJUST_MODE, (void *)(uintptr_t)(1 + s_zone), LV_SCR_LOAD_ANIM_NONE);
}

// Tap a boost tap-target (§3c — the invisible object at the end of the arc,
// replacing the old flanking icon buttons, which in turn replaced SCR_QUICK's
// "Boost heat"/"Boost cool" rows, that screen now gone) straight to the
// duration picker, packed exactly as the old quick-actions row packed it.
// user_data carries which end was tapped (1=heat, 0=cool). Neither tap
// target bubbles its event (the lv_obj default already), so a press here
// can't also reach the arc/screen underneath.
static void boost_btn_event_cb(lv_event_t *e)
{
    dial_state_stamp_input();
    dial_haptics_play(HAPTIC_TICK);
    bool heat = (bool)(uintptr_t)lv_event_get_user_data(e);
    uintptr_t packed = ((uintptr_t)s_zone << 1) | (heat ? 1u : 0u);
    ui_router_go(SCR_BOOST, (void *)packed, LV_SCR_LOAD_ANIM_NONE);
}

static void create(lv_obj_t *scr, void *arg)
{
    s_zone = (zone_idx_t)(uintptr_t)arg;
    s_shown_f = -1;
    s_knob_seq_start_f = -1;
    s_knob_seq_dir = 0;
    s_knob_seq_ms = 0;
    s_chevron_active = false;
    s_stale_shown = false;
    s_units_c = false;   // on_state (called right after create) sets the real value
    s_rel = false;
    s_relief_active = false;
    s_dragging = false;
    s_arc_min = s_arc_max = -1;   // force configure_arc_range() on this arc
    const dial_palette_t *pal = PAL();
    lv_obj_set_style_bg_color(scr, pal->bg, 0);

    // #2-3 Chassis ring / arc (r=165, w=16, 90deg gap at 6 o'clock).
    s_arc = lv_arc_create(scr);
    lv_obj_set_size(s_arc, 2 * ARC_R, 2 * ARC_R);
    lv_obj_center(s_arc);
    lv_arc_set_rotation(s_arc, 135);
    lv_arc_set_bg_angles(s_arc, 0, 270);
    lv_arc_set_range(s_arc, DIAL_TEMP_MIN_F, DIAL_TEMP_MAX_F);
    lv_arc_set_value(s_arc, (DIAL_TEMP_MIN_F + DIAL_TEMP_MAX_F) / 2);
    lv_obj_set_style_arc_width(s_arc, 16, LV_PART_MAIN);
    lv_obj_set_style_arc_width(s_arc, 16, LV_PART_INDICATOR);
    lv_obj_set_style_arc_rounded(s_arc, true, LV_PART_INDICATOR);
    lv_obj_set_style_bg_opa(s_arc, LV_OPA_TRANSP, LV_PART_KNOB);   // no built-in knob dot
    // The arc is DISPLAY-ONLY. An lv_arc grabs its whole bounding box (or, with
    // ADV_HITTEST, the entire ring) and turns any drag across it into a value
    // change — which is why a page-to-page swipe was also moving the setpoint.
    // Clearing CLICKABLE lets presses on the ring (and the centre) fall through
    // to the screen so they can be swipes/long-presses; the discrete handle
    // below is the only thing that sets temperature.
    lv_obj_clear_flag(s_arc, LV_OBJ_FLAG_CLICKABLE);

    // #4 Water level: a value-step overlay sharing the arc's exact geometry,
    // created after it so it lands on top of the fill. Rounded caps to match
    // every other arc on the face — a square end read as a different material
    // sitting on the ring rather than as part of it.
    s_level = lv_arc_create(scr);
    lv_obj_set_size(s_level, 2 * ARC_R, 2 * ARC_R);
    lv_obj_center(s_level);
    lv_arc_set_rotation(s_level, 135);
    lv_arc_set_bg_angles(s_level, 0, 270);
    lv_arc_set_angles(s_level, 0, 0);
    lv_obj_set_style_arc_opa(s_level, LV_OPA_TRANSP, LV_PART_MAIN);   // no second track
    lv_obj_set_style_arc_width(s_level, 16, LV_PART_INDICATOR);
    lv_obj_set_style_arc_rounded(s_level, true, LV_PART_INDICATOR);
    lv_obj_remove_style(s_level, NULL, LV_PART_KNOB);
    lv_obj_clear_flag(s_level, LV_OBJ_FLAG_CLICKABLE | LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_add_flag(s_level, LV_OBJ_FLAG_HIDDEN);   // until the first measurement

    // Neutral (level 0) landmark — a short tick at 12 o'clock over the arc
    // band, created after the arc so it sits above the fill. Shown only in
    // relative mode (apply_palette_and_state); the arc's own midpoint is
    // already at top, so this marks the center of the bipolar scale.
    s_zero_notch = lv_obj_create(scr);
    lv_obj_set_size(s_zero_notch, 3, 16);
    lv_obj_set_style_radius(s_zero_notch, 0, 0);
    lv_obj_set_style_border_width(s_zero_notch, 0, 0);
    lv_obj_set_style_bg_opa(s_zero_notch, LV_OPA_60, 0);
    lv_obj_clear_flag(s_zero_notch, LV_OBJ_FLAG_CLICKABLE | LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_align(s_zero_notch, LV_ALIGN_CENTER, 0, -ARC_R);
    lv_obj_add_flag(s_zero_notch, LV_OBJ_FLAG_HIDDEN);

    // #3c Boost glyphs capping the arc's two ends (owner: relocate the boost
    // controls off the dial face — "remove the boost iconbuttons where they
    // currently are and add just the icons to the end of the arc, and if the
    // tap target on the arc is the end of the arc where the icon is located
    // then it opens the set boost menu [the old icon buttons' behavior]").
    //
    // The arc sweeps 135deg (VALUE-MIN, bottom-left) clockwise to 45deg
    // (VALUE-MAX, bottom-right) — see value_from_point()/position_handle()
    // above for the same mapping. Cool sits at the min end, heat at the max
    // end: this continues both the arc's own semantics AND the left/right
    // split the old flanking buttons used.
    //
    // Two objects per side:
    //   - s_boost_*_icon: the glyph itself, now dial_font_icons_16 (owner,
    //     after seeing the 26px version on hardware: "icons don't look
    //     centered on the end of the arc" + "contain them within the arc's
    //     bounds, not overflowing"), centered on the arc band's actual
    //     centerline.
    //
    //     That centerline is NOT radius 165 (ARC_R). ARC_R is the arc
    //     OBJECT's half-size — LVGL draws the ring's OUTER edge there and
    //     grows the 16px stroke inward, not centered on it. Measured
    //     directly off a rendered PNG (a vertical pixel scan straight up
    //     from screen center, where nothing but the ring itself is present):
    //     ink runs from radius 165 down to ~150, i.e. the band is
    //     165(outer)-149(inner), centerline ~157 — matching, almost to the
    //     pixel, position_handle()'s own existing r = span/2 - indic_width/2
    //     = 165 - 8 = 157 (that function already had this right; it's why
    //     the handle itself sits correctly on the ring). Centering the icons
    //     on the OWNER-assumed 165 would put roughly half of each glyph
    //     outside the ring entirely, into bare background — the opposite of
    //     "contained within the arc's bounds" — so this uses the measured
    //     157, not 165. See the report for the full pixel measurement.
    //     Non-clickable — it's decoration; the tap target is the separate
    //     object below.
    //   - s_boost_*_tap: fully transparent, no border — the ACTUAL touch
    //     target, UNCHANGED by this pass (owner: leave it alone). lv_obj_
    //     set_ext_click_area() pads symmetrically, so simply padding the
    //     glyph would waste half of any extra reach off the glass past the
    //     bezel; instead this is a whole separate ~58px object centered
    //     further IN, at r=130 (outer edge r=159) — measured ink for the
    //     16px glyphs above runs r~150-164, so the tap target's outer rim
    //     still overlaps the glyph's inner half rather than missing it
    //     entirely now that the icon shrank. Opens SCR_BOOST on tap, packed
    //     exactly like the old buttons did.
    //
    // Z-ORDER / the min-max collision (owner flagged this trade-off going
    // in): the setpoint handle (#3b, created right below) rides the arc at
    // this same band and parks EXACTLY at 135deg/45deg at the range
    // extremes — squarely on top of these icons. LVGL hit-tests
    // topmost-child-first, so whichever of {handle, boost tap} was added to
    // the screen LAST wins a press landing in both hit boxes. This block
    // runs BEFORE the handle's own creation specifically so the handle stays
    // the later (topmost) object: at min/max the handle keeps full priority
    // and stays draggable, exactly as everywhere else on the ring. The boost
    // tap does NOT become unreachable there — it only loses the sliver of
    // its area that the handle's own ~28px hit-radius covers at that one
    // point of the ring, degrading to "harder to hit" (aim for the tap
    // target's inward bulk, away from the handle) — never "handle becomes
    // undraggable".
    // Backdrop discs. The glyphs are drawn ABOVE the arc and its fill (see
    // the move_foreground calls below), but a muted glyph painted straight
    // onto the bright fill blends into it and reads as being BEHIND the arc
    // (owner-reported twice — the second time after the stacking was already
    // proven correct, which is what identified it as contrast rather than
    // z-order). A small bg-coloured disc under each glyph punches a visual
    // notch in the ring, so the icon reads the same whether bare track or
    // full fill passes beneath it.
    s_boost_cool_pad = lv_obj_create(scr);
    lv_obj_set_size(s_boost_cool_pad, 26, 26);
    lv_obj_set_style_radius(s_boost_cool_pad, LV_RADIUS_CIRCLE, 0);
    lv_obj_set_style_border_width(s_boost_cool_pad, 2, 0);
    lv_obj_clear_flag(s_boost_cool_pad, LV_OBJ_FLAG_CLICKABLE | LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_align(s_boost_cool_pad, LV_ALIGN_CENTER, -111, 111);

    s_boost_heat_pad = lv_obj_create(scr);
    lv_obj_set_size(s_boost_heat_pad, 26, 26);
    lv_obj_set_style_radius(s_boost_heat_pad, LV_RADIUS_CIRCLE, 0);
    lv_obj_set_style_border_width(s_boost_heat_pad, 2, 0);
    lv_obj_clear_flag(s_boost_heat_pad, LV_OBJ_FLAG_CLICKABLE | LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_align(s_boost_heat_pad, LV_ALIGN_CENTER, 111, 111);

    s_boost_cool_icon = lv_label_create(scr);
    lv_obj_set_style_text_font(s_boost_cool_icon, &dial_font_icons_20, 0);
    lv_label_set_text(s_boost_cool_icon, DIAL_ICON_SNOW3);
    lv_obj_clear_flag(s_boost_cool_icon, LV_OBJ_FLAG_CLICKABLE | LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_align(s_boost_cool_icon, LV_ALIGN_CENTER, -111, 111);   // r=157 @ 135deg, exact

    s_boost_heat_icon = lv_label_create(scr);
    lv_obj_set_style_text_font(s_boost_heat_icon, &dial_font_icons_20, 0);
    lv_label_set_text(s_boost_heat_icon, DIAL_ICON_FLAME);
    lv_obj_clear_flag(s_boost_heat_icon, LV_OBJ_FLAG_CLICKABLE | LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_align(s_boost_heat_icon, LV_ALIGN_CENTER, 111, 111);   // r=157 @ 45deg, exact

    s_boost_cool_tap = lv_obj_create(scr);
    lv_obj_set_size(s_boost_cool_tap, 76, 76);
    lv_obj_set_style_radius(s_boost_cool_tap, LV_RADIUS_CIRCLE, 0);
    lv_obj_set_style_bg_opa(s_boost_cool_tap, LV_OPA_TRANSP, 0);
    lv_obj_set_style_border_width(s_boost_cool_tap, 0, 0);
    lv_obj_clear_flag(s_boost_cool_tap, LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_align(s_boost_cool_tap, LV_ALIGN_CENTER, -92, 92);
    lv_obj_add_event_cb(s_boost_cool_tap, boost_btn_event_cb, LV_EVENT_CLICKED, (void *)(uintptr_t)0);

    s_boost_heat_tap = lv_obj_create(scr);
    lv_obj_set_size(s_boost_heat_tap, 76, 76);
    lv_obj_set_style_radius(s_boost_heat_tap, LV_RADIUS_CIRCLE, 0);
    lv_obj_set_style_bg_opa(s_boost_heat_tap, LV_OPA_TRANSP, 0);
    lv_obj_set_style_border_width(s_boost_heat_tap, 0, 0);
    lv_obj_clear_flag(s_boost_heat_tap, LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_align(s_boost_heat_tap, LV_ALIGN_CENTER, 92, 92);
    lv_obj_add_event_cb(s_boost_heat_tap, boost_btn_event_cb, LV_EVENT_CLICKED, (void *)(uintptr_t)1);

    // Explicit z-order guarantee (owner, on hardware: "the boost icons dont
    // sit above the arc when its on"). Creation order already puts these
    // four objects after s_arc/s_level/s_zero_notch (all created above) —
    // verified against rendered pixels too: the glyph's own texture is
    // visible layered over the fill's rounded end-cap at the cool end in
    // dial.png, not replaced by solid fill colour, so nothing here was
    // literally painting over them. But that stacking was implicit (an
    // accident of where this block happened to sit in the function), and
    // what actually reads poorly there is low-opacity same-size glyph
    // sitting exactly on the fill's own rounded cap — a contrast problem,
    // not a hidden-behind one (see the colour tiers below, and the report
    // for the pixel evidence). Making the order explicit here removes any
    // ambiguity either way and survives a future reshuffle of this
    // function: these four move to front now, and the handle (created
    // right below) moves to front again after, so it stays topmost of the
    // whole group — required for it to keep winning both the draw AND the
    // hit-test at the 135deg/45deg extremes (see that comment above).
    lv_obj_move_foreground(s_boost_cool_pad);
    lv_obj_move_foreground(s_boost_heat_pad);
    lv_obj_move_foreground(s_boost_cool_icon);
    lv_obj_move_foreground(s_boost_heat_icon);
    lv_obj_move_foreground(s_boost_cool_tap);
    lv_obj_move_foreground(s_boost_heat_tap);

    // #3b Setpoint handle — the sole touch target for temperature. A thumb on
    // the ring at the current setpoint (created after the arc/fill so it sits on
    // top, at the fill's leading edge): press and drag it around the ring to set
    // the temperature. Its ext_click_area gives a generous ~56px grab without a
    // bulky visual. Deliberately NOT EVENT_BUBBLE-ing (the lv_obj default), so a
    // gesture that starts on it dies here instead of navigating — that, plus the
    // now display-only arc, is what makes swipe and temperature-set mutually
    // exclusive. Positioned/colored per render in apply_palette_and_state.
    s_handle = lv_obj_create(scr);
    lv_obj_set_size(s_handle, 28, 28);
    lv_obj_set_style_radius(s_handle, LV_RADIUS_CIRCLE, 0);
    lv_obj_set_style_border_width(s_handle, 3, 0);
    lv_obj_set_style_border_color(s_handle, pal->bg, 0);   // bg ring -> reads as a thumb ON the track
    lv_obj_clear_flag(s_handle, LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_add_flag(s_handle, LV_OBJ_FLAG_CLICKABLE);
    lv_obj_set_ext_click_area(s_handle, 14);   // ~56px effective touch target
    lv_obj_align(s_handle, LV_ALIGN_CENTER, 0, -ARC_R);
    lv_obj_add_event_cb(s_handle, handle_event_cb, LV_EVENT_PRESSED,    (void *)(uintptr_t)s_zone);
    lv_obj_add_event_cb(s_handle, handle_event_cb, LV_EVENT_PRESSING,   (void *)(uintptr_t)s_zone);
    lv_obj_add_event_cb(s_handle, handle_event_cb, LV_EVENT_RELEASED,   (void *)(uintptr_t)s_zone);
    lv_obj_add_event_cb(s_handle, handle_event_cb, LV_EVENT_PRESS_LOST, (void *)(uintptr_t)s_zone);
    lv_obj_move_foreground(s_handle);   // stays topmost of the whole group, see note above

    // #5 Side name.
    s_name_lbl = lv_label_create(scr);
    lv_obj_set_style_text_font(s_name_lbl, &lv_font_montserrat_16, 0);
    lv_label_set_text(s_name_lbl, s_zone == ZONE_A ? "RIGHT SIDE" : "LEFT SIDE");
    lv_obj_align(s_name_lbl, LV_ALIGN_CENTER, 0, 64 - CY);

    // #6 Identity underline (solid bar + dashed line variant, one shown).
    s_underline_solid = lv_obj_create(scr);
    lv_obj_set_size(s_underline_solid, 60, 3);
    lv_obj_set_style_radius(s_underline_solid, 0, 0);
    lv_obj_set_style_border_width(s_underline_solid, 0, 0);
    lv_obj_clear_flag(s_underline_solid, LV_OBJ_FLAG_CLICKABLE | LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_align(s_underline_solid, LV_ALIGN_CENTER, 0, 82 - CY);

    s_dash_pts[0] = (lv_point_t){ 0, 0 };
    s_dash_pts[1] = (lv_point_t){ 60, 0 };
    s_underline_dash = lv_line_create(scr);
    lv_line_set_points(s_underline_dash, s_dash_pts, 2);
    lv_obj_set_style_line_width(s_underline_dash, 3, 0);
    lv_obj_set_style_line_dash_width(s_underline_dash, 6, 0);
    lv_obj_set_style_line_dash_gap(s_underline_dash, 4, 0);
    lv_obj_set_style_line_rounded(s_underline_dash, false, 0);
    lv_obj_clear_flag(s_underline_dash, LV_OBJ_FLAG_CLICKABLE);
    lv_obj_align(s_underline_dash, LV_ALIGN_CENTER, 0, 82 - CY);
    lv_obj_add_flag(s_underline_dash, LV_OBJ_FLAG_HIDDEN);

    // #7 Water caption.
    s_water_lbl = lv_label_create(scr);
    lv_obj_set_style_text_font(s_water_lbl, &lv_font_montserrat_16, 0);
    lv_label_set_text(s_water_lbl, "WATER --");
    lv_obj_align(s_water_lbl, LV_ALIGN_CENTER, 0, 98 - CY);

    // #8 Setpoint numeral — fixed anchor box so digits never reflow.
    s_num_box = lv_obj_create(scr);
    lv_obj_set_size(s_num_box, 210, 92);
    lv_obj_set_style_bg_opa(s_num_box, LV_OPA_TRANSP, 0);
    lv_obj_set_style_border_width(s_num_box, 0, 0);
    lv_obj_clear_flag(s_num_box, LV_OBJ_FLAG_CLICKABLE | LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_align(s_num_box, LV_ALIGN_CENTER, 0, 150 - CY);

    s_temp_lbl = lv_label_create(s_num_box);
    lv_obj_set_style_text_font(s_temp_lbl, &dial_font_num_88, 0);
    lv_label_set_text(s_temp_lbl, "--");
    lv_obj_set_style_transform_pivot_x(s_temp_lbl, LV_PCT(50), 0);
    lv_obj_set_style_transform_pivot_y(s_temp_lbl, LV_PCT(50), 0);
    lv_obj_center(s_temp_lbl);

    // #9 Unit.
    s_unit_lbl = lv_label_create(scr);
    lv_obj_set_style_text_font(s_unit_lbl, &lv_font_montserrat_20, 0);
    lv_label_set_text(s_unit_lbl, "\xC2\xB0" "F");
    lv_obj_align(s_unit_lbl, LV_ALIGN_CENTER, 266 - CX, 122 - CY);

    // #10 State pill.
    s_pill = lv_obj_create(scr);
    lv_obj_set_height(s_pill, 26);
    lv_obj_set_width(s_pill, LV_SIZE_CONTENT);
    lv_obj_set_style_max_width(s_pill, 160, 0);
    lv_obj_set_style_radius(s_pill, 13, 0);
    lv_obj_set_style_border_width(s_pill, 1, 0);
    lv_obj_set_style_pad_left(s_pill, 12, 0);
    lv_obj_set_style_pad_right(s_pill, 12, 0);
    lv_obj_set_style_pad_column(s_pill, 6, 0);
    lv_obj_set_flex_flow(s_pill, LV_FLEX_FLOW_ROW);
    lv_obj_set_flex_align(s_pill, LV_FLEX_ALIGN_CENTER, LV_FLEX_ALIGN_CENTER, LV_FLEX_ALIGN_CENTER);
    lv_obj_clear_flag(s_pill, LV_OBJ_FLAG_SCROLLABLE);
    // CLICKABLE starts cleared (lv_obj_create's own default is ON — this
    // undoes that) and ext_click_area starts at 0: both are toggled on
    // ONLY while relief is active, in apply_palette_and_state, so a tap on
    // an inert Holding/Until chip falls through to whatever's underneath
    // instead of doing something surprising.
    lv_obj_clear_flag(s_pill, LV_OBJ_FLAG_CLICKABLE);
    lv_obj_align(s_pill, LV_ALIGN_CENTER, 0, 214 - CY);
    // The handler itself is a no-op unless relief is active (see
    // pill_event_cb) — registering it unconditionally here is harmless
    // since it can only ever fire while CLICKABLE is actually set.
    lv_obj_add_event_cb(s_pill, pill_event_cb, LV_EVENT_CLICKED, NULL);

    s_pill_glyph = lv_label_create(s_pill);
    lv_obj_set_style_text_font(s_pill_glyph, &lv_font_montserrat_16, 0);
    lv_label_set_text(s_pill_glyph, LV_SYMBOL_MINUS);

    s_pill_word = lv_label_create(s_pill);
    lv_obj_set_style_text_font(s_pill_word, &lv_font_montserrat_16, 0);
    lv_label_set_text(s_pill_word, "--");

    // Trailing close mark (§3) — stock symbol font, since LV_SYMBOL_CLOSE is
    // only in the Montserrat faces, not the boost icon font. Hidden by
    // default (apply_palette_and_state shows it only during relief); a third
    // flex child, so it just falls in after the word with the pill's own
    // pad_column gap, no extra layout needed.
    s_pill_close = lv_label_create(s_pill);
    lv_obj_set_style_text_font(s_pill_close, &lv_font_montserrat_16, 0);
    lv_label_set_text(s_pill_close, LV_SYMBOL_CLOSE);
    lv_obj_add_flag(s_pill_close, LV_OBJ_FLAG_HIDDEN);

    // #11 Power disc — now the ONLY control on this row (owner: the boost
    // controls have moved onto the arc ends, see #3c above; the row they
    // used to flank this button on is otherwise empty). Short tap toggles
    // power (CLICKED); long-press opens the Schedule/Hold picker
    // (LONG_PRESSED, §2) — see power_long_press_cb for how the two are kept
    // from BOTH firing on one long press. 72px (owner pass 3, from an
    // earlier boost-button layout pass now superseded) is this project's own
    // >=72px round-screen touch floor, so this is the smallest the disc can
    // go without becoming the exception to a rule it usually enforces on
    // OTHER elements; left unpadded (no ext_click_area) so it doesn't eat
    // into the "Update available" label's own clearance just below it (the
    // tighter budget in this row now — see that label's own comment).
    s_power_btn = dial_btn_create(scr);
    lv_obj_set_size(s_power_btn, 72, 72);
    lv_obj_set_style_radius(s_power_btn, LV_RADIUS_CIRCLE, 0);
    lv_obj_set_style_border_width(s_power_btn, 2, 0);
    lv_obj_align(s_power_btn, LV_ALIGN_CENTER, 0, 280 - CY);
    lv_obj_add_event_cb(s_power_btn, power_event_cb, LV_EVENT_CLICKED, (void *)(uintptr_t)s_zone);
    lv_obj_add_event_cb(s_power_btn, power_long_press_cb, LV_EVENT_LONG_PRESSED, NULL);
    s_power_glyph = lv_label_create(s_power_btn);
    lv_obj_set_style_text_font(s_power_glyph, &lv_font_montserrat_28, 0);
    lv_label_set_text(s_power_glyph, LV_SYMBOL_POWER);
    lv_obj_center(s_power_glyph);

    // #12 Staleness dot.
    s_stale_dot = lv_obj_create(scr);
    lv_obj_set_size(s_stale_dot, 10, 10);
    lv_obj_set_style_radius(s_stale_dot, LV_RADIUS_CIRCLE, 0);
    lv_obj_set_style_border_width(s_stale_dot, 0, 0);
    lv_obj_clear_flag(s_stale_dot, LV_OBJ_FLAG_CLICKABLE | LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_align(s_stale_dot, LV_ALIGN_CENTER, 0, 26 - CY);
    // Never LV_OBJ_FLAG_HIDDEN: lv_obj_fade_in/out (used from apply_palette_
    // and_state) only animate opacity, so visibility must be opacity-driven
    // the whole time or fade_in would animate an object LVGL still skips.
    lv_obj_set_style_opa(s_stale_dot, LV_OPA_TRANSP, 0);

    // #13 Page dots — 3 (Dial(A) - Dial(B) - Menu), evenly spaced
    // 16px apart around the same centered slot the original 2-dot pair used.
    s_dot_a = lv_obj_create(scr);
    lv_obj_set_size(s_dot_a, 6, 6);
    lv_obj_set_style_radius(s_dot_a, LV_RADIUS_CIRCLE, 0);
    lv_obj_set_style_border_width(s_dot_a, 0, 0);
    lv_obj_clear_flag(s_dot_a, LV_OBJ_FLAG_CLICKABLE | LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_align(s_dot_a, LV_ALIGN_CENTER, 164 - CX, 340 - CY);

    s_dot_b = lv_obj_create(scr);
    lv_obj_set_size(s_dot_b, 6, 6);
    lv_obj_set_style_radius(s_dot_b, LV_RADIUS_CIRCLE, 0);
    lv_obj_set_style_border_width(s_dot_b, 0, 0);
    lv_obj_clear_flag(s_dot_b, LV_OBJ_FLAG_CLICKABLE | LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_align(s_dot_b, LV_ALIGN_CENTER, 180 - CX, 340 - CY);

    s_dot_menu = lv_obj_create(scr);
    lv_obj_set_size(s_dot_menu, 6, 6);
    lv_obj_set_style_radius(s_dot_menu, LV_RADIUS_CIRCLE, 0);
    lv_obj_set_style_border_width(s_dot_menu, 0, 0);
    lv_obj_clear_flag(s_dot_menu, LV_OBJ_FLAG_CLICKABLE | LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_align(s_dot_menu, LV_ALIGN_CENTER, 196 - CX, 340 - CY);

    // Away badge — tiny, hidden unless st->away (design-spec.md §7 extension).
    s_away_lbl = lv_label_create(scr);
    lv_obj_set_style_text_font(s_away_lbl, &lv_font_montserrat_12, 0);
    lv_label_set_text(s_away_lbl, "AWAY");
    lv_obj_clear_flag(s_away_lbl, LV_OBJ_FLAG_CLICKABLE | LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_align(s_away_lbl, LV_ALIGN_CENTER, 180 - CX, 44 - CY);
    lv_obj_add_flag(s_away_lbl, LV_OBJ_FLAG_HIDDEN);

    // OTA notice — dual-purpose (see apply_palette_and_state): the M6
    // pending-verify "Finalizing update..." caption, and (owner
    // reassessment) the ambient "Update available" indicator. Both tiny,
    // both hidden unless their own condition holds. Parked in the one
    // genuinely dead patch of this carefully-laid-out face rather than a new
    // region: the gap between the power disc's bottom edge (#11, now
    // 280+36=316 since the owner-pass-3 shrink) and the page dots (#13,
    // y=340) sits squarely inside the arc's own
    // 90deg gap at 6 o'clock (#2), the same void the disc and dots already
    // share — and neither state this label carries claims the slot
    // permanently (pending_verify is gone within ~30s of boot; the update
    // notice disappears the moment the update is installed, skipped, or
    // night falls).
    s_ota_lbl = lv_label_create(scr);
    lv_obj_set_style_text_font(s_ota_lbl, &lv_font_montserrat_12, 0);
    lv_obj_set_style_text_align(s_ota_lbl, LV_TEXT_ALIGN_CENTER, 0);
    lv_label_set_text(s_ota_lbl, "Finalizing update...");
    lv_obj_clear_flag(s_ota_lbl, LV_OBJ_FLAG_CLICKABLE | LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_align(s_ota_lbl, LV_ALIGN_CENTER, 0, 330 - CY);
    lv_obj_add_flag(s_ota_lbl, LV_OBJ_FLAG_HIDDEN);
    // Touch target for the "Update available" state only (CLICKABLE is
    // added/removed per-render, same idiom as s_pill above). ext_click_area
    // mirrors the exact value the setpoint handle uses (#3b above) — this
    // project's established trick for reaching a legal target off a small
    // visual element — but capped there rather than pushed toward this
    // project's >=72px floor: this slot sits immediately below the power
    // disc's own un-padded hit box (bottom edge now y=316, since the
    // owner-pass-3 shrink — more clearance to this label's own top edge
    // than the original 88px disc had), so any more padding here starts
    // stealing power-toggle taps off the disc's bottom rim. Effective target
    // ends up
    // well over 72px wide (the text alone) by ~43px tall — short of 72px
    // tall for that reason, the same kind of documented shortfall this file
    // already accepts for the handle itself (~56px there, see #3b).
    lv_obj_set_ext_click_area(s_ota_lbl, 14);
    lv_obj_add_event_cb(s_ota_lbl, ota_notice_cb, LV_EVENT_CLICKED, NULL);
}

static void destroy(void)
{
    // Kill anims targeting our objects before the router frees them.
    if (s_temp_lbl)   lv_anim_del(s_temp_lbl, NULL);
    if (s_num_box)    lv_anim_del(s_num_box, NULL);
    if (s_arc)        lv_anim_del(s_arc, NULL);
    if (s_pill_glyph) lv_anim_del(s_pill_glyph, NULL);
    if (s_stale_dot)  lv_anim_del(s_stale_dot, NULL);
    if (s_boost_timer) { lv_timer_del(s_boost_timer); s_boost_timer = NULL; }

    s_actual_f = -1.0f;

    s_level = NULL;
    s_zero_notch = NULL;
    s_handle = NULL;
    s_dragging = false;
    s_knob_seq_start_f = -1;
    s_knob_seq_dir = 0;
    s_knob_seq_ms = 0;
    s_arc = s_stale_dot = s_name_lbl = NULL;
    s_underline_solid = s_underline_dash = s_water_lbl = NULL;
    s_num_box = s_temp_lbl = s_unit_lbl = NULL;
    s_pill = s_pill_glyph = s_pill_word = s_pill_close = NULL;
    s_power_btn = s_power_glyph = NULL;
    s_boost_cool_pad = s_boost_heat_pad = NULL;
    s_boost_cool_icon = s_boost_cool_tap = NULL;
    s_boost_heat_icon = s_boost_heat_tap = NULL;
    s_dot_a = s_dot_b = s_dot_menu = NULL;
    s_away_lbl = NULL;
    s_ota_lbl = NULL;
    s_chevron_active = false;
    s_stale_shown = false;
}

// Ticks once a second while the shown zone's relief is active, just to
// recompute the pill's mm:ss text — everything else it touches is idempotent.
static void boost_timer_cb(lv_timer_t *t)
{
    (void)t;
    if (!s_arc) return;
    app_state_t st;
    dial_state_get(&st);
    apply_palette_and_state(&st);
}

static void on_state(const app_state_t *st)
{
    if (!s_arc || !st->have_state) return;
    const zone_state_t *z = &st->zones[s_zone];

    // Optimistic intent wins while set; otherwise follow the device. Resolved
    // BEFORE apply_palette_and_state, which lays the water stripes out against
    // s_shown_f — reading a stale target there would leave them a poll behind.
    // Skipped entirely while the handle is being dragged: the finger owns
    // s_shown_f then, and a commit landing mid-drag must not yank it away.
    if (!s_dragging) {
        int f = (st->ui_temp_f[s_zone] >= 0) ? st->ui_temp_f[s_zone] : dial_c_to_f(z->temp_c);
        s_shown_f = f;
    }

    // Sets s_units_c (among other things) before render_numeral below reads it
    // — otherwise a units toggle would render one call stale. (Also repositions
    // the handle, unless a drag is in progress.)
    apply_palette_and_state(st);

    if (!s_dragging) {
        lv_arc_set_value(s_arc, s_shown_f);
        render_numeral(s_shown_f);
    }

    if (z->user_name[0]) {
        char name[36];
        snprintf(name, sizeof(name), "%s'S SIDE", z->user_name);
        // Upper-case for the label style (ASCII only — names come from Orion).
        for (char *p = name; *p; p++) if (*p >= 'a' && *p <= 'z') *p -= 32;
        lv_label_set_text(s_name_lbl, name);
    }

    // Countdown ticker: created on the transition into relief, deleted on the
    // transition out (or in destroy() if the screen is torn down first).
    if (z->relief_active && !s_boost_timer) {
        s_boost_timer = lv_timer_create(boost_timer_cb, 1000, NULL);
    } else if (!z->relief_active && s_boost_timer) {
        lv_timer_del(s_boost_timer);
        s_boost_timer = NULL;
    }
}

static bool on_knob(int detents)
{
    if (!s_arc || s_shown_f < 0) return false;

    // A boost is a modal thing you started deliberately (owner decision): while
    // relief is active the knob is inert, so a stray detent can't rewrite the
    // setpoint under the counting-down pill. Consumed (returns true) with a
    // stop cue, never applied.
    if (s_relief_active) {
        dial_haptics_play_soft(HAPTIC_STOP);
        return true;
    }

    int dir = detents > 0 ? 1 : -1;
    uint32_t now_ms = lv_tick_get();
    if (s_knob_seq_start_f < 0 || s_knob_seq_dir != dir ||
        (uint32_t)(now_ms - s_knob_seq_ms) > RAIL_BOOST_SEQ_MS) {
        s_knob_seq_start_f = s_shown_f;
        s_knob_seq_dir = dir;
    }
    s_knob_seq_ms = now_ms;

    // Relative: one detent = exactly one level in the turned direction, from
    // whatever level is displayed (dial_rel_step snaps an off-grid value onto
    // the grid as it moves, so the numeral and the bed always move together).
    // Absolute: one detent = 1°F, clamped to s_arc_min/s_arc_max — the same
    // device-reported (or fallback) rails configure_arc_range() just set,
    // read back here rather than re-deriving them, since this branch only
    // runs when s_rel is false (so s_arc_min/max already hold the absolute
    // range, not the relative one).
    int nf;
    bool rail_boost;
    if (s_rel) {
        int cur = dial_rel_from_f(s_shown_f);
        int raw = cur + detents;
        rail_boost = raw < DIAL_REL_MIN || raw > DIAL_REL_MAX;
        nf = dial_rel_step(s_shown_f, detents);
    } else {
        int raw = s_shown_f + detents;
        rail_boost = raw < s_arc_min || raw > s_arc_max;
        nf = raw;
        if (nf < s_arc_min) nf = s_arc_min;
        if (nf > s_arc_max) nf = s_arc_max;
    }
    if (rail_boost) {
        bool heat = dir > 0;
        int prev_f = (s_knob_seq_start_f >= s_arc_min && s_knob_seq_start_f <= s_arc_max)
                     ? s_knob_seq_start_f : s_shown_f;
        dial_haptics_play(HAPTIC_CONFIRM);
        dial_state_set_relief_optimistic_prev_f(
            s_zone, true, heat,
            (int64_t)time(NULL) * 1000 + (int64_t)RAIL_BOOST_MINUTES * 60000,
            prev_f);
        app_cmd_t cmd = { .kind = CMD_BOOST_START, .zone = s_zone,
                          .temp_f = prev_f, .a = heat ? 1 : 0,
                          .b = RAIL_BOOST_MINUTES };
        dial_cmd_post(&cmd);
        s_knob_seq_start_f = -1;
        s_knob_seq_dir = 0;
        return true;
    }
    if (nf == s_shown_f) {                          // pinned at the range stop
        dial_haptics_play_soft(HAPTIC_STOP);
        anim_nudge(s_num_box, dir);
        anim_nudge(s_arc, dir);
        return true;
    }

    lv_arc_set_value(s_arc, nf);
    s_shown_f = nf;
    render_numeral(nf);
    level_render(nf);
    position_handle(nf);
    anim_zoom_bump(s_temp_lbl);
    post_temp(nf);
    return true;
}

// Face order: Dial(B) <-left- Dial(A) <-left- Menu. zone_b is the LEFT side of
// the bed and zone_a the RIGHT, so the chain now reads left-to-right the way
// the bed does. A single-zone topper has no partner face: its one dial sits
// where the pair would, and a left swipe goes straight to the menu.
//
// Boost and the Schedule/Hold picker open via tap/long-press on the icon
// buttons and power disc, not a swipe on the dial itself (see
// boost_btn_event_cb / power_long_press_cb) — up/down are simply unhandled
// here now that the router forwards all four directions.
static bool on_gesture(lv_dir_t dir)
{
    if (dir != LV_DIR_LEFT && dir != LV_DIR_RIGHT) return false;
    // Never navigate while the setpoint handle is being dragged. The handle
    // doesn't bubble gestures so this shouldn't fire mid-drag, but a swipe that
    // grazes it must not both move the temperature and change pages.
    if (s_dragging) return false;

    app_state_t st;
    dial_state_get(&st);
    bool dual = dial_state_is_dual(&st);

    if (dir == LV_DIR_LEFT) {
        if (dual && s_zone == ZONE_B) {
            // Commit the side choice BEFORE navigating: the nav policy follows
            // ui_zone, so an uncommitted swipe would be undone by the next
            // state commit (the poll would yank the view back).
            dial_state_set_ui_zone(ZONE_A);
            ui_router_go(SCR_DIAL, (void *)(uintptr_t)ZONE_A, LV_SCR_LOAD_ANIM_MOVE_LEFT);
        } else {
            // End of the dial chain (or the only dial there is) — the menu face
            // is a step further left.
            ui_router_go(SCR_MENU, NULL, LV_SCR_LOAD_ANIM_MOVE_LEFT);
        }
        return true;
    }

    // RIGHT walks back toward Dial(B). From the leftmost face there's nothing
    // further right, so leave the gesture unconsumed rather than fake a move.
    if (dual && s_zone == ZONE_A) {
        dial_state_set_ui_zone(ZONE_B);
        ui_router_go(SCR_DIAL, (void *)(uintptr_t)ZONE_B, LV_SCR_LOAD_ANIM_MOVE_RIGHT);
        return true;
    }
    return false;
}

const ui_screen_t scr_dial = {
    .create = create, .destroy = destroy, .on_state = on_state,
    .on_knob = on_knob, .on_gesture = on_gesture,
};
