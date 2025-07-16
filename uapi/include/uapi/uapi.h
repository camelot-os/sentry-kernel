// SPDX-FileCopyrightText: 2023-2024 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/*
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


#ifndef __SENTRY_UAPI_UAPI_H
#define __SENTRY_UAPI_UAPI_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include "handle.h"
#include "types.h"

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/**
 * Return the effective max usable size in bytes in SVC Exchange area.
 *
 * a valid variable.
 */
size_t svcexchange_get_maxlen(void);

/**
 * Copy data to svc_exchange area
 *
 * # Safety
 *
 * Callers must ensure memory pointed to by `from` up to `from + length` belongs to
 * a valid variable.
 */
Status copy_to_kernel(const uint8_t *from, size_t length);

/**
 * Copy data from svc_exchange area to user-controlled buffer
 *
 * # Safety
 *
 * Callers must ensure memory pointed to by `from` up to `from + length` belongs to
 * a valid variable.
 */
Status copy_from_kernel(uint8_t *to, size_t length);

/**
 * Clear overall svc_exchange area with default 0x0 pattern
 *
 * CAUTION: be sure that all required data has already been copied before calling this API
 */
Status clean_svcexchange(void);

/**
 * Send a SIGALRM signal to the task after `timeout_ms` milliseconds.
 */
Status __sys_alarm(uint32_t timeout_ms);

/**
 * Exiting the process.
 *
 * POSIX upper layers (libshield): void _exit(int status);
 */
Status __sys_exit(int32_t status);

/**
 * Retrieve number of cycles since boot (u64)
 */
Status __sys_get_cycle(Precision precision);

/**
 * Get back a given device handle from DTS auto-generated device identifier
 */
Status __sys_get_device_handle(uint8_t devlabel);

/**
 * Get back a given DMA stream handle from DTS auto-generated device identifier
 */
Status __sys_get_dma_stream_handle(uint32_t label);

/**
 * Get back a given SHM handle from SHM label defined in DTS
 */
Status __sys_get_shm_handle(uint32_t shmlabel);

/**
 * Get global identifier for a given process label
 *
 * This mechanism allows respawn detection, as the label is fixed but the resource identifier
 * is regenerated.
 * A process is a resource like any other and communicating with it requires to get
 * back its resource handle from its label.
 *
 * POSIX upper layer(s): N/A
 */
Status __sys_get_process_handle(ProcessLabel process);

/**
 * Retrieve a random number (u32)
 */
Status __sys_get_random(void);

/**
 * configure value of given GPIO associated to given  device ressource
 */
Status __sys_gpio_configure(uint32_t resource, uint8_t io);

/**
 * get value of given GPIO associated to given  device ressource
 */
Status __sys_gpio_get(uint32_t resource, uint8_t io);

/**
 * reset value of given GPIO associated to given  device ressource
 */
Status __sys_gpio_reset(uint32_t resource, uint8_t io);

/**
 * set value of given GPIO associated to given  device ressource
 */
Status __sys_gpio_set(uint32_t resource, uint8_t io, bool val);

/**
 * toggle value of given GPIO associated to given  device ressource
 */
Status __sys_gpio_toggle(uint32_t resource, uint8_t io);

/**
 * acknowledge at interrupt controller level the given interrupt
 */
Status __sys_irq_acknowledge(uint16_t irq);

/**
 * enable (unmask) at interrupt controller level the given interrupt
 */
Status __sys_irq_enable(uint16_t irq);

/**
 * disable (mask) at interrupt controller level the given interrupt
 */
Status __sys_irq_disable(uint16_t irq);


/**
 * Send a message from the current task's 'svc_exchange area' through
 * the UART.
 */
Status __sys_log(size_t length);

/**
 * Configure the CPU's sleep behaviour.
 *
 * The `mode` parameters toggles between the two traditional wake-up
 * modes for ARM CPUs:
 * - wait for interrupt (`wfi`)
 * - wait for event (`wfe`)
 *
 * it also accepts two other mode values that enable or prevent the
 * CPU from sleeping.
 */
Status __sys_manage_cpu_sleep(CPUSleep mode);

/**
 *  Map a mappable device.
 *
 * POSIX upper layer(s): mmap(2)
 *   * addr can be null or set to ressource addr
 *   * fd must be equal to ressource handle
 *   * prot, offset and flags are ignored for now
 */
Status __sys_map_dev(devh_t dev);

/**
 *  Map a mappable SHM.
 *
 * POSIX upper layer(s): shmget(2) (key == handle)
 */
Status __sys_map_shm(shmh_t shm);

/**
 * Send events to another process
 */
Status __sys_send_ipc(uint32_t resource, uint8_t length);

/**
 * Send a signal to another process
 */
Status __sys_send_signal(uint32_t resource, Signal signal_type);

/**
 * Set SHM permissions. shm_open() is considered automatic as declared in dtsi, handle is generated.
 *
 * POSIX upper layer(s): shmctl(3),
 */
Status __sys_shm_set_credential(shmh_t shm, taskh_t target, uint32_t shm_perm);

/**
 * Get SHM informations
 */
Status __sys_shm_get_infos(shmh_t shm);


/**
 * Sleep for a given amount of time
 *
 * POSIX upper layer(s): sleep(3), usleep(3)
 */
Status __sys_sleep(SleepDuration duration_ms, SleepMode mode);

/**
 * Start another task, if capability added and other process allowed to be started by us
 *
 * - POSIX upper layer(s): execv()
 */
Status __sys_start(ProcessLabel process);

/**
 * Unmap a mapped device.
 *
 * POSIX upper layer(s): munmap(2)
 *   addr must match the ressource addr (ressource handle to be found in userspace from the addr?)
 *   length must match the ressource size
 */
Status __sys_unmap_dev(devh_t dev);

/**
 * Unmap a mapped device.
 *
 * POSIX upper layer(s): TBD
 */
Status __sys_unmap_shm(shmh_t shm);

/**
 * Wait for input event. Single active blocking syscall.
 *
 * This syscall holds the current thread as long as none of the event requested
 * in the given event mask is received.
 *
 * The event source (a device for an interrupt, a PID for an IPC or signal) can be set.
 * Setting the source to 0 means that any source is allowed.
 *
 * If received, event informations are set in the task SVC data
 * structure and the function returns `Status::Ok`.
 *
 * This function must be the single blocking point of the function (excepting
 * sleep() case)
 *
 * POSIX upper layer(s): select(2), poll(2)
 */
Status __sys_wait_for_event(uint8_t mask, int32_t timeout);

/**
 * Release the processor before the end of the current quantum.
 * Allows triggering a schedule() even if not in the process's central blocking point
 *
 * POSIX upper layer(s): N/A
 */
Status __sys_sched_yield(void);

Status __sys_pm_set_clock(uint32_t clk_reg, uint32_t regmsk, uint32_t val);

Status __sys_dma_start_stream(dmah_t stream);

Status __sys_dma_suspend_stream(dmah_t stream);

Status __sys_dma_resume_stream(dmah_t stream);

Status __sys_dma_assign_stream(dmah_t stream);

Status __sys_dma_unassign_stream(dmah_t stream);

Status __sys_dma_get_stream_status(dmah_t stream);

Status __sys_dma_get_stream_info(dmah_t stream);

#if CONFIG_BUILD_TARGET_AUTOTEST
Status __sys_autotest_set_capa(uint32_t capa);

Status __sys_autotest_clear_capa(uint32_t capa);
#endif

#ifdef __cplusplus
} // extern "C"
#endif // __cplusplus

#endif /* __SENTRY_UAPI_UAPI_H */
