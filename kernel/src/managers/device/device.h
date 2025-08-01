// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef PRIVATE_DEVICE_H
#define PRIVATE_DEVICE_H

#ifdef __cplusplus
extern "C" {
#endif

#define HANDLE_DEVICE 1UL

/**
 * @file device private handle manipulation API
 */
#include <assert.h>
#include <inttypes.h>
#include <sentry/ktypes.h>
#include <sentry/managers/security.h>

typedef struct device {
    devinfo_t           devinfo;      /**< device info (info shared with userspace) */
    capability_t        capability;   /**< device associated capability */
    uint32_t            clk_id;       /**< clock identifier, as defined in dts */
    uint32_t            bus_id;       /**< bus identifier, as defined in dts */
    uint32_t            owner;        /**< label of the owner. To be fullfill by app using the sentry,owner dts flag */
} device_t;

typedef struct kdevh {
    uint32_t dev_cap : 12; /**< device capability (unique capa per device) */
    uint32_t reserved : 1; /**< reserved field */
    uint32_t id : 16;      /**< device unique identifier on the system */
    uint32_t family : 3;   /**< handle familly */
} kdevh_t;

static_assert(sizeof(kdevh_t) == sizeof(uint32_t), "device opaque sizing failed!");

union udh {
    const devh_t *dh;
    const kdevh_t *kdh;
};

/**
 * NOTE: the union usage that allows a target memory to be multiple typed is not
 * FramaC compliant. To define if we aim to use a FramaC sprcific code for proof model
 * (meaning that these very API is out of the proof) or using a FramaC compliant API,
 * requiring a copy of the value instead of a local trans-typing
 * XXX: such usage is an UB in C++, meaning that it will be problematic in that case
 * these API are strictly dedicated to device internals and as such should not be included in
 * A C++ based test. A possibility is to add something like:
 * #ifdef __cplusplus
 * #error "Incompatible with C++ direct usage"
 * #endif
 */

 /**
  * @fn devh_to_kdevh convert an opaque dev handler to a structured handler
  *
  * @param dh input dev handler
  *
  * @return converted handler to structured value
  */
static inline const kdevh_t *devh_to_kdevh(const devh_t * const dh) {
    /*@ assert \valid(dh); */
    union udh converter = {
        .dh = dh
    };
    return converter.kdh;
}

 /**
  * @fn kdevh_to_devh convert a structured dev handler to an opaque handler
  *
  * @param kdh input structured dev handler
  *
  * @return converted handler to opaque value
  */
static inline const devh_t *kdevh_to_devh(const kdevh_t * const kdh) {
    /*@ assert \valid(kdh); */
    union udh converter = {
        .kdh = kdh
    };
    return converter.dh;
}

static inline devh_t forge_devh(const device_t * const device)
{
        /*@ assert \valid_read(device); */
    kdevh_t kdevh = {
        .dev_cap = device->capability & CAP_DEV_MASK,
        .reserved = 0,
        .id = device->devinfo.id,
        .family = HANDLE_DEVICE,
    };
    union udh converter = {
        .kdh = &kdevh
    };
    return *converter.dh;
}

#ifdef __cplusplus
}
#endif

#endif/*!PRIVATE_DEVICE_H*/
