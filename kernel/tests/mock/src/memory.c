// SPDX-FileCopyrightText: 2025 Camelot OSS team
// SPDX-License-Identifier: Apache-2.0

#include <sys/mman.h>
#include <unistd.h>
#include <string.h>
#include <stdbool.h>
#include <stdlib.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <sentry/ktypes.h>

#define MMU_PAGE_SIZE 4096UL

/* set static to be used by unmap_kdev */
static void * map;
static size_t mapsize;
static bool mapped = false;

/* mocked external APIs (out of EXTI module)*/
kstatus_t mgr_mm_map_kdev(uint32_t addr, size_t size)
{
    mapsize = ((size / MMU_PAGE_SIZE) + 1);
    kstatus_t res = K_STATUS_OKAY;

    if (mapped == true) {
        res = K_ERROR_BADSTATE;
        goto err;
    }
    map = mmap((void*)addr, 4096UL, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
    if (map != (void*)addr) {
        if ((size_t)map > addr) {
            printf("Unable to map device to correct address 0x%h\n", addr);
            goto err;
        }
        /* the kernel may have align the mapping on 4k size */
        if ((size_t)map + 4096 < (addr + 0x400)) {
            printf("Unable to map device to correct address 0x%h\n", addr);
            printf("Page alignment problem not resolvable\n");
            printf("address is 0x%h\n\n", map);
            printf(strerror(errno));
            goto err;
        }
        /* page-alignment do include the device*/
    }
    if (map == (void*)-1) {
        printf("mmap has failed ! %s\n", strerror(errno));
        goto err;
    }
    /*
     * push reset values (0x0 for EXTI= in the device. Using standard memory mapping size of device,
     * portable to any STM32 for offset
     */
    memset((void*)addr, 0x0, size);
    mapped = true;
    res = K_STATUS_OKAY;
err:
    return res;
}

kstatus_t mgr_mm_unmap_kdev(void) {
    kstatus_t res = K_ERROR_BADSTATE;
    if (mapped != true) {
        goto err;
    }
    munmap(map, mapsize);
    res = K_STATUS_OKAY;
err:
    return res;
}
