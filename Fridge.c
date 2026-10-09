/*
 * PIC-Based Smart Refrigerator Inventory and Food Safety Monitoring System
 */
#pragma config FOSC = HS
#pragma config WDTE = OFF
#pragma config PWRTE = OFF
#pragma config BOREN = OFF
#pragma config LVP = OFF
#pragma config CPD = OFF
#pragma config WRT = OFF
#pragma config CP = OFF

#include <xc.h>
#include <stdint.h>

#define _XTAL_FREQ 4000000

#include "lcd_fridge.h"

/* TUNABLE SETTINGS */
#define SECONDS_PER_DAY         10UL
#define TEMP_HIGH_X10           80
#define TEMP_HYST_X10           5
#define TEMP_ALARM_DELAY_S      10
#define DOOR_ALARM_S            15
#define EXPIRING_SOON_DAYS      1
#define WARN_ON_EXPIRING_SOON   1
#define MAX_SHELF_DAYS          30

#define DOOR_CLOSED_MEANS_OPEN          0
#define PRODUCT_CLOSED_MEANS_PRESENT    1

#define PAGE_TIME_100MS     20
#define UI_TIMEOUT_S        20
#define DEBOUNCE_TICKS      3
#define REPEAT_DELAY        60
#define REPEAT_PERIOD       15

#define LED_GREEN   RB0
#define LED_RED     RB1
#define BUZZER      RB2

#define NUM_PROD    3
#define NUM_IN      7
enum { IN_NEXT = 0, IN_OK, IN_BACK, IN_DOOR, IN_MILK, IN_EGGS, IN_JUICE };

enum { P_EMPTY = 0,
       P_SETUP,
       P_PRESENT,
       P_REMOVED,
       P_OUT_TEMP };

#define W_TEMP      0x01
#define W_DOOR      0x02
#define W_PROD0     0x04

enum { UI_HOME = 0, UI_DETAIL, UI_SETUP, UI_DECIDE };

enum { PG_WARN = 0, PG_PROD, PG_HOME };

typedef struct {
    uint8_t  state;
    uint8_t  popup;
    uint8_t  shelf;
    uint32_t secs_left;
} Product;

static Product prod[NUM_PROD];

static volatile uint8_t pending10 = 0;

static uint8_t stable[NUM_IN];
static uint8_t cnt[NUM_IN];
static uint8_t hold[3];
static uint8_t ev_press[3];
static uint8_t ev_rep[3];

static uint16_t temp_x10 = 0;
static uint8_t  temp_alarm = 0;
static uint16_t temp_high_secs = 0;
static uint8_t  door_open = 0;
static uint16_t door_secs = 0;

static uint8_t active_mask = 0;
static uint8_t ack_mask = 0;

static uint8_t c10 = 0, c100 = 0, beat = 0;

static uint8_t ui_mode = UI_HOME;
static uint8_t ui_prod = 0;
static uint8_t ui_choice = 0;
static uint8_t ui_idle = 0;
static uint8_t page_idx = 0;
static uint8_t page_timer = 0;
static uint8_t need_render = 1;
static uint8_t door_msg_ticks = 0;
static uint8_t prev_product_state[3];

static char l1[17], l2[17], l3[17], l4[17];
static char shown1[17], shown2[17], shown3[17], shown4[17];
static char *wbuf;
static uint8_t wp;

static uint8_t raw_in(uint8_t i)
{
    switch (i) {
        case IN_NEXT:  return (RA5 == 0);
        case IN_OK:    return (RE0 == 0);
        case IN_BACK:  return (RE1 == 0);
        case IN_DOOR:  return (RA1 == 0);
        case IN_MILK:  return (RA2 == 0);
        case IN_EGGS:  return (RA3 == 0);
        default:       return (RA4 == 0);
    }
}

static void inputs_init(void)
{
    uint8_t i;
    for (i = 0; i < NUM_IN; i++) { stable[i] = raw_in(i); cnt[i] = 0; }
    for (i = 0; i < 3; i++) { hold[i] = 0; ev_press[i] = 0; ev_rep[i] = 0; prev_product_state[i] = stable[IN_MILK + i]; }
}

static void inputs_scan(void)
{
    uint8_t i, r;
    for (i = 0; i < NUM_IN; i++) {
        r = raw_in(i);
        if (r == stable[i]) {
            cnt[i] = 0;
        } else if (++cnt[i] >= DEBOUNCE_TICKS) {
            stable[i] = r;
            cnt[i] = 0;
            if (i < 3 && r) { ev_press[i] = 1; ev_rep[i] = 1; hold[i] = 0; }
            need_render = 1;
        }
        if (i < 3 && stable[i]) {
            if (hold[i] < 255) hold[i]++;
            if (hold[i] >= REPEAT_DELAY) {
                ev_rep[i] = 1;
                hold[i] = REPEAT_DELAY - REPEAT_PERIOD;
            }
        }
    }
}

static uint8_t door_is_open(void)
{
#if DOOR_CLOSED_MEANS_OPEN
    return stable[IN_DOOR];
#else
    return !stable[IN_DOOR];
#endif
}

static uint8_t prod_present(uint8_t i)
{
#if PRODUCT_CLOSED_MEANS_PRESENT
    return stable[IN_MILK + i];
#else
    return !stable[IN_MILK + i];
#endif
}

static uint16_t read_temp_x10(void)
{
    uint8_t n;
    uint16_t sum = 0, adc;
    for (n = 0; n < 8; n++) {
        __delay_us(30);
        ADCON0bits.GO_nDONE = 1;
        while (ADCON0bits.GO_nDONE) ;
        adc = ((uint16_t)ADRESH << 8) | ADRESL;
        sum += adc;
    }
    adc = sum >> 3;

    return (uint16_t)(((uint32_t)adc * 5000UL) / 1023UL);
}

static uint8_t default_shelf(uint8_t i)
{
    if (i == 0) return 7;
    if (i == 1) return 14;
    return 10;
}

static uint8_t is_tracked(uint8_t i)
{
    uint8_t s = prod[i].state;
    return (s == P_PRESENT || s == P_REMOVED || s == P_OUT_TEMP);
}

static uint8_t needs_action(uint8_t i)
{
    return (prod[i].state == P_SETUP || prod[i].state == P_REMOVED);
}

static uint8_t expiry_state(uint8_t i)
{
    if (prod[i].secs_left == 0) return 2;
    if (prod[i].secs_left <= (uint32_t)EXPIRING_SOON_DAYS * SECONDS_PER_DAY) return 1;
    return 0;
}

static uint16_t days_left(uint8_t i)
{
    return (uint16_t)((prod[i].secs_left + SECONDS_PER_DAY - 1UL) / SECONDS_PER_DAY);
}

static void products_update(void)
{
    uint8_t i, present;

    if (!door_open) return;

    for (i = 0; i < NUM_PROD; i++) {
        present = prod_present(i);
        switch (prod[i].state) {
            case P_EMPTY:
                if (present) {
                    prod[i].state = P_SETUP;
                    prod[i].shelf = default_shelf(i);
                    prod[i].popup = 1;
                    need_render = 1;
                }
                break;
            case P_SETUP:
                if (!present) {
                    prod[i].state = P_EMPTY;
                    prod[i].popup = 0;
                    need_render = 1;
                }
                break;
            case P_PRESENT:
                if (!present) {
                    prod[i].state = P_REMOVED;
                    prod[i].popup = 1;
                    need_render = 1;
                }
                break;
            case P_REMOVED:
            case P_OUT_TEMP:
                if (present) {
                    prod[i].state = P_PRESENT;
                    prod[i].popup = 0;
                    need_render = 1;
                }
                break;
            default:
                break;
        }
    }
}

static void warnings_update(void)
{
    uint8_t mask = 0, i, e;

    if (temp_alarm) mask |= W_TEMP;
    if (door_secs >= DOOR_ALARM_S) mask |= W_DOOR;

    for (i = 0; i < NUM_PROD; i++) {
        if (is_tracked(i)) {
            e = expiry_state(i);
#if WARN_ON_EXPIRING_SOON
            if (e) mask |= (uint8_t)(W_PROD0 << i);
#else
            if (e == 2) mask |= (uint8_t)(W_PROD0 << i);
#endif
        }
    }
    active_mask = mask;
    ack_mask &= mask;
}

static void update_outputs(void)
{
    uint8_t unacked = (uint8_t)(active_mask & (uint8_t)~ack_mask);

    if (active_mask == 0) {
        LED_GREEN = 1; LED_RED = 0; BUZZER = 0;
    } else {
        LED_GREEN = 0; LED_RED = 1;
        BUZZER = (unacked && (beat & 0x02)) ? 1 : 0;
    }
}

static void b_start(char *buf) { wbuf = buf; wp = 0; }
static void b_chr(char c)      { if (wp < 16) wbuf[wp++] = c; }
static void b_str(const char *s) { while (*s) b_chr(*s++); }
static void b_end(void)        { while (wp < 16) wbuf[wp++] = ' '; wbuf[16] = 0; }

static void b_u16(uint16_t v, uint8_t zpad)
{
    char t[5];
    uint8_t n = 0;
    do { t[n++] = (char)('0' + (v % 10)); v /= 10; } while (v && n < 5);
    while (n < zpad && n < 5) t[n++] = '0';
    while (n) b_chr(t[--n]);
}

static void b_temp(uint16_t t)
{
    b_u16(t / 10, 1);
    b_chr('.');
    b_chr((char)('0' + (t % 10)));
}

static void b_name(uint8_t i)
{
    if (i == 0) b_str("MILK");
    else if (i == 1) b_str("EGGS");
    else b_str("JUICE");
}

static void b_code(uint8_t i)
{
    uint8_t e;
    switch (prod[i].state) {
        case P_EMPTY:   b_str("--"); break;
        case P_SETUP:   b_str("NW"); break;
        case P_REMOVED:
        case P_OUT_TEMP: b_str("RM"); break;
        default:
            e = expiry_state(i);
            if (e == 2) b_str("EX");
            else if (e == 1) b_str("SO");
            else b_str("OK");
            break;
    }
}

static void screen_home(void)
{

    b_start(l1);
    b_str("MILK: ");
    if (prod[0].state == P_PRESENT || prod[0].state == P_REMOVED || prod[0].state == P_OUT_TEMP)
        { b_u16(days_left(0), 1); b_str("D"); }
    else if (prod[0].state == P_SETUP)
        b_str("NEW");
    else
        b_str("--");
    b_end();

    b_start(l2);
    b_str("EGGS: ");
    if (prod[1].state == P_PRESENT || prod[1].state == P_REMOVED || prod[1].state == P_OUT_TEMP)
        { b_u16(days_left(1), 1); b_str("D"); }
    else if (prod[1].state == P_SETUP)
        b_str("NEW");
    else
        b_str("--");
    b_end();

    b_start(l3);
    b_str("JUICE: ");
    if (prod[2].state == P_PRESENT || prod[2].state == P_REMOVED || prod[2].state == P_OUT_TEMP)
        { b_u16(days_left(2), 1); b_str("D"); }
    else if (prod[2].state == P_SETUP)
        b_str("NEW");
    else
        b_str("--");
    b_end();

    b_start(l4);
    b_str("DOOR: ");
    if (door_open) b_str("OPEN");
    else b_str("CLOSED");
    b_end();
}

static void screen_door_locked(void)
{
    b_start(l1);
    b_str("OPEN DOOR FIRST");
    b_end();

    b_start(l2);
    b_end();

    b_start(l3);
    b_end();

    b_start(l4);
    b_end();
}

static void screen_warning(uint8_t b, uint8_t k, uint8_t n)
{
    uint8_t i;

    b_start(l1);
    b_str("*** WARNING ***");
    b_end();

    b_start(l2);
    if (b == 0) {
        b_str("HIGH TEMPERATURE");
    } else if (b == 1) {
        b_str("DOOR IS OPEN");
    } else {
        i = (uint8_t)(b - 2);
        b_name(i);
        if (expiry_state(i) == 2)
            b_str(" EXPIRED");
        else
            b_str(" EXPIRING");
    }
    b_end();

    b_start(l3);
    if (b == 0) {
        b_str("TEMP: ");
        b_temp(temp_x10);
        b_str("C");
    } else if (b == 1) {
        b_str("OPEN TIME: ");
        b_u16(door_secs, 1);
        b_str("S");
    } else {
        i = (uint8_t)(b - 2);
        b_name(i);
        b_str(": ");
        b_u16(days_left(i), 1);
        b_str("D LEFT");
    }
    b_end();

    b_start(l4);
    if (b == 0)
        b_str("CHECK TEMP");
    else if (b == 1)
        b_str("CLOSE DOOR");
    else
        b_str("CHECK ITEM");
    b_end();
}

static void screen_product(uint8_t i)
{
    uint8_t e;

    b_start(l1);
    b_name(i);
    switch (prod[i].state) {
        case P_EMPTY:    b_str(": ---"); break;
        case P_SETUP:    b_str(" NEW"); break;
        case P_PRESENT:  b_str(" PRESENT"); break;
        case P_REMOVED:  b_str(" REMOVED"); break;
        default:         b_str(" TAKEN OUT"); break;
    }
    b_end();

    b_start(l2);
    switch (prod[i].state) {
        case P_EMPTY:   b_str("OUT OF STOCK"); break;
        case P_SETUP:   b_str("OK: SET EXPIRY"); break;
        case P_PRESENT:
            e = expiry_state(i);
            if (e == 2) {
                b_str("EXPIRED!");
            } else {
                b_str("EXPIRES IN "); b_u16(days_left(i), 1); b_chr('d');
                if (e == 1) b_str(" !");
            }
            break;
        default:        b_str("OK:RET/CONSUMED"); break;
    }
    b_end();

    b_start(l3);
    if (door_open) b_str("DOOR: OPEN");
    else b_str("DOOR: CLOSED");
    b_end();

    b_start(l4);
    b_str("NXT/OK/BACK");
    b_end();
}

static void screen_setup(void)
{
    b_start(l1);
    b_name(ui_prod); b_str(" EXPIRES IN");
    b_end();

    b_start(l2);
    b_u16(prod[ui_prod].shelf, 2); b_str("D NXT+ OK=SAVE");
    b_end();

    b_start(l3);
    b_str("DOOR MUST OPEN");
    b_end();

    b_start(l4);
    b_str("BACK=CANCEL");
    b_end();
}

static void screen_decide(void)
{
    b_start(l1);
    b_str("REMOVED: NXT/OK");
    b_end();

    b_start(l2);
    b_str("> "); b_name(ui_prod); b_chr(' ');
    if (ui_choice) b_str("CONSUMED"); else b_str("RETURNED");
    b_end();

    b_start(l3);
    b_str("NXT=CHANGE");
    b_end();

    b_start(l4);
    b_str("OK=SAVE BACK=EXIT");
    b_end();
}

static void screen_rotation(void)
{
    uint8_t pt[9], pa[9];
    uint8_t cnt_p = 0, nw = 0, b, i;

    for (b = 0; b < 5; b++) {
        if (active_mask & (1 << b)) { pt[cnt_p] = PG_WARN; pa[cnt_p] = b; cnt_p++; nw++; }
    }
    for (i = 0; i < NUM_PROD; i++) {
        if (needs_action(i)) { pt[cnt_p] = PG_PROD; pa[cnt_p] = i; cnt_p++; }
    }
    pt[cnt_p] = PG_HOME; pa[cnt_p] = 0; cnt_p++;

    if (page_idx >= cnt_p) page_idx = 0;

    if (pt[page_idx] == PG_WARN)      screen_warning(pa[page_idx], (uint8_t)(page_idx + 1), nw);
    else if (pt[page_idx] == PG_PROD) screen_product(pa[page_idx]);
    else                              screen_home();
}

static uint8_t differs(char *a, char *b)
{
    uint8_t i;
    for (i = 0; i < 16; i++) if (a[i] != b[i]) return 1;
    return 0;
}

static void lcd_update(void)
{
    uint8_t i;
    if (differs(l1, shown1)) {
        for (i = 0; i < 17; i++) shown1[i] = l1[i];
        Lcd_Set_Cursor(1, 1);
        Lcd_Write_String(l1);
    }
    if (differs(l2, shown2)) {
        for (i = 0; i < 17; i++) shown2[i] = l2[i];
        Lcd_Set_Cursor(2, 1);
        Lcd_Write_String(l2);
    }
    if (differs(l3, shown3)) {
        for (i = 0; i < 17; i++) shown3[i] = l3[i];
        Lcd_Set_Cursor(3, 1);
        Lcd_Write_String(l3);
    }
    if (differs(l4, shown4)) {
        for (i = 0; i < 17; i++) shown4[i] = l4[i];
        Lcd_Set_Cursor(4, 1);
        Lcd_Write_String(l4);
    }
}

static void render(void)
{
    if (door_msg_ticks > 0) {
        screen_door_locked();
        lcd_update();
        return;
    }

    switch (ui_mode) {
        case UI_DETAIL: screen_product(ui_prod); break;
        case UI_SETUP:  screen_setup(); break;
        case UI_DECIDE: screen_decide(); break;
        default:        screen_rotation(); break;
    }
    lcd_update();
}

static void ui_go_home(void)
{
    ui_mode = UI_HOME;
    page_idx = 0;
    page_timer = 0;
    ui_idle = 0;
    need_render = 1;
}

static void open_prompt(uint8_t i)
{
    uint8_t s = prod[i].state;
    if (s == P_SETUP) {
        ui_mode = UI_SETUP;
    } else if (s == P_REMOVED || s == P_OUT_TEMP) {
        ui_mode = UI_DECIDE;
        ui_choice = 0;
    } else {
        return;
    }
    ui_prod = i;
    ui_idle = 0;
    need_render = 1;
}

static void ui_buttons(void)
{
    uint8_t nxt, nxt_rep, ok, back, i;

    nxt = ev_press[0]; nxt_rep = ev_rep[0]; ok = ev_press[1]; back = ev_press[2];
    ev_press[0] = ev_press[1] = ev_press[2] = 0;
    ev_rep[0] = ev_rep[1] = ev_rep[2] = 0;

    if (!(nxt || nxt_rep || ok || back)) return;
    ui_idle = 0;
    need_render = 1;

    switch (ui_mode) {
        case UI_HOME:
            if (back) ack_mask = active_mask;
            if (nxt) { ui_mode = UI_DETAIL; ui_prod = 0; }
            if (ok) {
                for (i = 0; i < NUM_PROD; i++) {
                    if (needs_action(i)) { open_prompt(i); break; }
                }
            }
            break;

        case UI_DETAIL:
            if (nxt) { ui_prod++; if (ui_prod >= NUM_PROD) ui_go_home(); }
            else if (back) ui_go_home();
            else if (ok) open_prompt(ui_prod);
            break;

        case UI_SETUP:
            if (nxt_rep) {
                prod[ui_prod].shelf++;
                if (prod[ui_prod].shelf > MAX_SHELF_DAYS) prod[ui_prod].shelf = 1;
            } else if (ok) {
                prod[ui_prod].secs_left = (uint32_t)prod[ui_prod].shelf * SECONDS_PER_DAY;
                prod[ui_prod].state = P_PRESENT;
                ui_go_home();
            } else if (back) {
                ui_go_home();
            }
            break;

        case UI_DECIDE:
            if (nxt) {
                ui_choice ^= 1;
            } else if (ok) {
                if (ui_choice == 0) {
                    if (prod[ui_prod].state == P_REMOVED) prod[ui_prod].state = P_OUT_TEMP;
                } else {
                    prod[ui_prod].state = P_EMPTY;
                    prod[ui_prod].secs_left = 0;
                }
                ui_go_home();
            } else if (back) {
                ui_go_home();
            }
            break;

        default:
            break;
    }
}

static void ui_task(void)
{
    uint8_t i;

    if (ui_mode == UI_SETUP && prod[ui_prod].state != P_SETUP) ui_go_home();
    if (ui_mode == UI_DECIDE &&
        prod[ui_prod].state != P_REMOVED && prod[ui_prod].state != P_OUT_TEMP) ui_go_home();

    if (ui_mode == UI_HOME || ui_mode == UI_DETAIL) {
        for (i = 0; i < NUM_PROD; i++) {
            if (prod[i].popup) {
                prod[i].popup = 0;
                open_prompt(i);
                if (ui_mode == UI_SETUP || ui_mode == UI_DECIDE) break;
            }
        }
    }
}

static void on_second(void)
{
    uint8_t i;

    temp_x10 = read_temp_x10();

    if (temp_x10 > TEMP_HIGH_X10) {
        if (temp_high_secs < 65535) temp_high_secs++;
        if (temp_high_secs >= TEMP_ALARM_DELAY_S) temp_alarm = 1;
    } else {
        temp_high_secs = 0;
        if (temp_x10 <= TEMP_HIGH_X10 - TEMP_HYST_X10) temp_alarm = 0;
    }

    if (door_open) { if (door_secs < 65535) door_secs++; }
    else door_secs = 0;

    for (i = 0; i < NUM_PROD; i++) {
        if (is_tracked(i) && prod[i].secs_left > 0) prod[i].secs_left--;
    }

    if (ui_mode != UI_HOME) {
        if (++ui_idle >= UI_TIMEOUT_S) ui_go_home();
    }
}

static void on_100ms(void)
{
    beat++;

    if (door_msg_ticks > 0) {
        door_msg_ticks--;
        need_render = 1;
    }
    warnings_update();
    update_outputs();

    if (ui_mode == UI_HOME) {
        if (++page_timer >= PAGE_TIME_100MS) { page_timer = 0; page_idx++; }
    }
    need_render = 1;

    if (++c100 >= 10) { c100 = 0; on_second(); }
}

static void on_10ms(void)
{
    uint8_t i;

    inputs_scan();
    door_open = door_is_open();

    if (!door_open) {
        for (i = 0; i < NUM_PROD; i++) {
            if (prev_product_state[i] && !stable[IN_MILK + i]) {
                door_msg_ticks = 15;
                need_render = 1;
            }
        }
    }

    for (i = 0; i < NUM_PROD; i++)
        prev_product_state[i] = stable[IN_MILK + i];

    products_update();

    if (++c10 >= 10) { c10 = 0; on_100ms(); }
}

#define TMR1_COUNTS   (_XTAL_FREQ / 4UL / 8UL / 100UL)
#define TMR1_RELOAD   (65536UL - TMR1_COUNTS)

static void hw_init(void)
{
    ADCON1 = 0x8E;
    ADCON0 = 0x81;

    TRISA = 0xFF;
    TRISB = 0x00;
    TRISD = 0x00;
    TRISE = 0x07;

    PORTB = 0x00;
    PORTD = 0x00;
}

static void timer1_start(void)
{
    T1CON = 0x30;
    TMR1H = (uint8_t)(TMR1_RELOAD >> 8);
    TMR1L = (uint8_t)(TMR1_RELOAD & 0xFF);
    PIR1bits.TMR1IF = 0;
    PIE1bits.TMR1IE = 1;
    INTCONbits.PEIE = 1;
    INTCONbits.GIE = 1;
    T1CONbits.TMR1ON = 1;
}

void __interrupt() isr(void)
{
    if (PIR1bits.TMR1IF) {
        PIR1bits.TMR1IF = 0;
        TMR1H = (uint8_t)(TMR1_RELOAD >> 8);
        TMR1L = (uint8_t)(TMR1_RELOAD & 0xFF);
        if (pending10 < 250) pending10++;
    }
}

void main(void)
{
    uint8_t i;

    hw_init();
    Lcd_Init();
    Lcd_Clear();

    for (i = 0; i < NUM_PROD; i++) {
        prod[i].state = P_EMPTY;
        prod[i].popup = 0;
        prod[i].shelf = default_shelf(i);
        prod[i].secs_left = 0;
    }
    shown1[0] = 0; shown2[0] = 0; shown3[0] = 0; shown4[0] = 0;

    b_start(l1); b_str("FRIDGE MONITOR"); b_end();
    b_start(l2); b_str("STARTING..."); b_end();
    b_start(l3); b_end();
    b_start(l4); b_end();
    lcd_update();
    __delay_ms(1500);

    inputs_init();
    temp_x10 = read_temp_x10();
    door_open = door_is_open();

    timer1_start();

    while (1) {
        while (pending10) {
            INTCONbits.GIE = 0;
            pending10--;
            INTCONbits.GIE = 1;
            on_10ms();
        }
        ui_buttons();
        ui_task();
        if (need_render) {
            need_render = 0;
            render();
        }
    }
}
