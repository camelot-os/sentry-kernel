// SPDX-FileCopyrightText: 2024 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef DRIVERS_TIMER_H
#define DRIVERS_TIMER_H

int timer_init(void);

int timer_enable(void);

int timer_release(void);

int timer_enable_interrupt(void);

int timer_disable_interrupt(void);

int timer_interrupt_acknowledge(void);

int timer_restart(void);

uint8_t timer_get_irqn(void);

Status timer_map(devh_t *handle);

Status timer_unmap(devh_t handle);

int timer_set_periodic(void);

#endif/*! DRIVERS_TIMER_H */
