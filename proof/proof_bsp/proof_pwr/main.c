#include <inttypes.h>
#include <sentry/ktypes.h>
#include <bsp/drivers/clk/pwr.h>
#include <sentry/arch/asm-cortex-m/layout.h>
#include "../framac_tools.h"

volatile uint32_t regvalue;

int main(void)
{
    /* Initialize device with randomness (over-approximation of
       all content possibilities, avoid first device access ioread32()
       uninitialized-read red alarms.
    */
    memset((void*)PWR_BASE_ADDR, Frama_C_entropy_source_32, 0x20);

    pwr_probe();
    return 0;
}
