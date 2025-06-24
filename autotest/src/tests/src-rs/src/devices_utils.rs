// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::devices_dt::{DEVICE_NAMES, DEVICES, SHM_NAMES, SHMS};
use sentry_uapi::systypes::dev::DevInfo;
use sentry_uapi::systypes::shm::ShmInfo;

/// Search for a device by its name
pub fn get_device_by_name(name: &str) -> Option<&'static DevInfo> {
    DEVICE_NAMES
        .iter()
        .position(|&n| n == name)
        .map(|i| &DEVICES[i])
}
/// Iterate over all devices
pub fn iter_devices() -> impl Iterator<Item = (&'static str, &'static DevInfo)> {
    DEVICE_NAMES.iter().copied().zip(DEVICES.iter())
}

/// Get SHM by name
pub fn get_shm_by_name(name: &str) -> Option<&'static ShmInfo> {
    SHM_NAMES.iter().position(|&n| n == name).map(|i| &SHMS[i])
}
