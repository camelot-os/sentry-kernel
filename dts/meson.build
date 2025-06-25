# SPDX-License-Identifier: Apache-2.0
#
# Copyright 2025 Ledger SAS
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

dtsi_files = files(
  'sentry.dtsi'
)

install_data(
  dtsi_files,
  install_dir: get_option('datadir') + '/dts',
  install_tag: 'devel',
)

examples_dts_files = files(
  'examples/nucleo_f401re.dts',
  'examples/nucleo_l476rg_autotest.dts',
  'examples/nucleo_l476rg_debug.dts',
  'examples/nucleo_l476rg.dts',
  'examples/nucleo_u5a5_autotest.dts',
  'examples/nucleo_u5a5.dts',
  'examples/nucleo_u5a5_nooutput.dts',
  'examples/nucleo_wb55_autotest.dts',
  'examples/stm32f429i_disc1_autotest.dts',
  'examples/stm32f429i_disc1_debug.dts',
  'examples/stm32f429i_disc1.dts',
  'examples/stm32f429i_disc1_release.dts',
  'examples/opentitan_earlgrey.dts',
)

install_data(
  examples_dts_files,
  follow_symlinks: false,
  install_dir: get_option('datadir') + '/dts/board',
  install_tag: 'devel',
)
