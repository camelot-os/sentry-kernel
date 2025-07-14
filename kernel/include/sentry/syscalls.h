// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef SYSCALLS_H
#define SYSCALLS_H

#include <uapi/handle.h>
#include <uapi/types.h>
#include <sentry/ktypes.h>
#include <sentry/arch/asm-generic/thread.h>

stack_frame_t *gate_send_ipc(stack_frame_t *frame, taskh_t target, uint32_t len);

stack_frame_t *gate_waitforevent(stack_frame_t *frame, uint8_t mask, int32_t timeout);

stack_frame_t *gate_send_signal(stack_frame_t *frame, taskh_t target, uint32_t signal);

stack_frame_t *gate_gpio_set(stack_frame_t *frame, devh_t devhandle, uint8_t io, bool val);

stack_frame_t *gate_gpio_get(stack_frame_t *frame, devh_t devhandle, uint8_t io);

stack_frame_t *gate_gpio_reset(stack_frame_t *frame, devh_t devhandle, uint8_t io);

stack_frame_t *gate_gpio_toggle(stack_frame_t *frame, devh_t devhandle, uint8_t io);

stack_frame_t *gate_gpio_configure(stack_frame_t *frame, devh_t devhandle, uint8_t io);

stack_frame_t *gate_get_devhandle(stack_frame_t *frame, uint8_t devid);

stack_frame_t *gate_get_shmhandle(stack_frame_t *frame, uint32_t shmid);

stack_frame_t *gate_int_acknowledge(stack_frame_t *frame, uint16_t IRQn);

stack_frame_t *gate_int_enable(stack_frame_t *frame, uint16_t IRQn);

stack_frame_t *gate_int_disable(stack_frame_t *frame, uint16_t IRQn);

stack_frame_t *gate_map_dev(stack_frame_t *frame, devh_t device);

stack_frame_t *gate_unmap_dev(stack_frame_t *frame, devh_t device);

stack_frame_t *gate_map_shm(stack_frame_t *frame, shmh_t shm);

stack_frame_t *gate_unmap_shm(stack_frame_t *frame, shmh_t shm);

stack_frame_t *gate_shm_setcreds(stack_frame_t *frame, shmh_t shm, taskh_t target, SHMPermission perms);

stack_frame_t *gate_exit(const stack_frame_t *frame, uint32_t result);

stack_frame_t *gate_get_prochandle(stack_frame_t *frame, uint32_t job_label);

stack_frame_t *gate_yield(stack_frame_t *frame);

stack_frame_t *gate_sleep(stack_frame_t *frame, uint32_t duration_ms, uint32_t sleep_mode);

stack_frame_t *gate_start(stack_frame_t *frame, uint32_t target_label);

stack_frame_t *gate_get_random(stack_frame_t *frame);

stack_frame_t *gate_pm_manage(stack_frame_t *frame, uint32_t pm_command);

stack_frame_t *gate_pm_clock_set(stack_frame_t *frame, uint32_t clk_reg, uint32_t clkmsk, uint32_t val);

stack_frame_t *gate_alarm(stack_frame_t *frame, uint32_t delay_ms, uint32_t flag);

stack_frame_t *gate_get_cycle(stack_frame_t *frame, uint32_t precision);

stack_frame_t *gate_log(stack_frame_t *frame, __MAYBE_UNUSED uint32_t log_len);

stack_frame_t *gate_get_dmahandle(stack_frame_t *frame, uint32_t streamlabel);

stack_frame_t *gate_shm_get_infos(stack_frame_t *frame, shmh_t shm);

stack_frame_t *gate_dma_getinfo(stack_frame_t *frame, dmah_t dmah);

stack_frame_t *gate_dma_assign(stack_frame_t *frame, dmah_t dmah);

stack_frame_t *gate_dma_unassign(stack_frame_t *frame, dmah_t dmah);

stack_frame_t *gate_dma_start(stack_frame_t *frame, dmah_t dmah);

stack_frame_t *gate_dma_suspend(stack_frame_t *frame, dmah_t dmah);

stack_frame_t *gate_dma_resume(stack_frame_t *frame, dmah_t dmah);

#if CONFIG_BUILD_TARGET_AUTOTEST
stack_frame_t *gate_autotest_set_self_capa(stack_frame_t *frame, uint32_t capa);

stack_frame_t *gate_autotest_clear_self_capa(stack_frame_t *frame, uint32_t capa);
#endif

#endif/*!SYSCALLS_H*/
