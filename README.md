<!--
SPDX-FileCopyrightText: 2023-2024 Ledger SAS
SPDX-License-Identifier: Apache-2.0
-->

![sentry logo](https://sentry-kernel.readthedocs.io/en/latest/_images/sentry_kernel.png)

# About

[![OpenSSF Best Practices](https://www.bestpractices.dev/projects/10498/badge)](https://www.bestpractices.dev/projects/10498)
![GNU/Linux build](https://github.com/camelot-os/sentry-kernel/actions/workflows/gnulinux.yml/badge.svg)
![MacOS X build](https://github.com/camelot-os/sentry-kernel/actions/workflows/macos.yml/badge.svg)
![Frama-C RTE Analysis](https://github.com/camelot-os/sentry-kernel/actions/workflows/proof.yml/badge.svg)
[![Documentation Status](https://readthedocs.org/projects/sentry-kernel/badge/?version=latest)](https://sentry-kernel.readthedocs.io/en/latest/?badge=latest)
![GitHub Release](https://img.shields.io/github/v/release/camelot-os/sentry-kernel)
![GitHub License](https://img.shields.io/github/license/camelot-os/sentry-kernel)
[![REUSE status](https://api.reuse.software/badge/github.com/camelot-os/sentry-kernel)](https://api.reuse.software/info/github.com/camelot-os/sentry-kernel)

The Sentry kernel is a high security level micro-kernel implementation made for high security embedded systems that include micro-controllers in association with dedicated Secure Element component for security cryptographic functions.

Complete Sentry documentation is published on [readthedocs](https://sentry-kernel.readthedocs.io/en/latest/index.html).

Sentry kernel uses [The Meson Build System](https://mesonbuild.com/).

# Prerequisites

## Tools installation
Before building the project, one needs to install the build system and related tool. This project use the meson reference implementation in python. All dependencies are described in `requirements.txt`.

```console
pip3 install -r requirements.txt
```

## Cross Toolchain

This kernel aims to be fully portable. Its initial target are ARM Cortex-M MCUs (starting with STM32) and thus one needs a cross toolchain for such target. One can use any cross toolchain as long as this is a GNU compatible compiler for Cortex-M. The reference toolchain used for `CI/CD` is bundled in this project using `meson` wrap mechanism.

Cross-toolchain relative need to be declared so that the `meson` build system is able to detect overall cross-compilers and associated tools. This is
done by defining `cross-files`. The meson build system describes these cross file [here](https://mesonbuild.com/Cross-compilation.html).

As this project is using both C and Rust, it is required to set some specific flags in the cross-file(s) you use.

### About the host machine

The host machine is the environment in which the Sentry kernel is executed. This is one of the three standard machines definitions:

   * the build machine is the host in which the complitation is made
   * the target machine is the compiler-internal environment that is used during compilation step
   * the host machine is the host in which the compilation result is being executed

This is required to declare the host machine as a `none` type, as there is no runtime bellow Sentry. In the same way, this is not a `bare-metal` system, as this keyword is considered by Rust as
an environment in which it is possible to link the `std` crate, which is not true as a Sentry application environment by now.

As a consequence, the following fields must be set in the `[host_machine]` block:
```yaml
system = 'none'
kernel = 'none'
```

### Cross-compilation triples

The usage of C (using gcc) and Rust (using LLVM frontend) requires to specify both the Gcc cross-triple prefix value and the llvm triple.
This values are set as typical `[constants]` fields, for e.g.:

```yaml
cross_triple = 'arm-none-eabi'
# llvm triple, target-explicit, needed by Rust
llvm_triple = 'thumbv8m.main-none-eabi'
```

It is then possible to set the gcc toolchain prefix in the very same `[constants]` block with something like:

```yaml
cross_toolchain = '/path/to/gcc-cross/'
cross_compile = cross_toolchain + 'bin/' + cross_triple + '-'
```

These constants can be used in the `[binaries]` declaration block, with the following:

```yaml
c = cross_compile + 'gcc'
cpp = cross_compile + 'g++'
ar = cross_compile + 'gcc-ar'
ranlib = cross_compile + 'gcc-ranlib'
strip = cross_compile + 'strip'
objcopy = cross_compile + 'objcopy'
rust = ['rustc', '--target=' + llvm_triple]
```

The Rust linker also needs to be specified to be homogeneous to the C linker (being GNU ld), using the `rust_ld` binary definition:

```yaml
rust_ld = c
```

Typical functional meson cross-files can be found [here](https://github.com/camelot-os/meson-cross-files/tree/main).

## Project bootstrap

A common good practice is `do not inject environment variable for build configuration`. For this purpose, `meson` does not allow using relative path in toolchain definition. Toolchain path **_must_** be absolute.

One needs to deliver to the `meson` build system the kernel configuration based on Kconfig. This can be done with
kconfiglib that is listed in `requirements.txt. The kernel configuration is generated into a local `.config` file that
holds the complete kernel configuration, and that is used at build time to select the corresponding sources and features.

#### Using defconfigs

defconfig files are stored in configs/ directory and can be used directly. In that case, the defconfig must be parsed in order to
forge a `.config` file. This file is then passed to the `config` option at setup time:

```console
defconfig configs/stm32f4_debug_defconfig
meson setup -Dconfig=.config [...]
```
If a complete config file is used, it can be directly passed to the `config` option.

#### Setting custom configurations

Generating the configuration is made using the standard Linux Kconfig UI. This interface can be called by ninja by targetting the kconfig module's menuconfig target:
```console
ninja -C builddir kconfig@@menuconfig
```

Or by calling `menuconfig` directly. This, one need to have kconfig venv set correctly (`srctree` and `subprojects`).
This can be done by using Meson [`devenv`](https://mesonbuild.com/Commands.html#devenv)
```console
meson devenv -C builddir
menuconfig
```

# How to build

## About build options

The Sentry kernel has the following configuration options, that can be added at `meson setup` time using `-D<optname>=<optvalue>`

   * `with_doc` (boolean, false): Enable support for building docs
   * `with_tests` (boolean, false): Enable unit test suite support through `meson test`
   * `with_proof` (boolean, false): Enable support for frama-C analysis through `meson test`
   * `with_kernel` (boolean, true): Enable kernel binary build
   * `with_uapi` (boolean, true): Enable kernel UAPI library build
   * `with_idle` (boolean, true): Enable kernel Idle task build
   * `with_tools` (boolean, true): Enable build host native tooling build
   * `rust-channel` (string): Set the rust channel. Minimal version required is 1.86.
   * `config`: (string): path to the defconfig file. Can be externally provided, while respecting the kernel Kconfig
   * `dts` (string): DTS file path, may be local or any externaly provided DTS file
   * `dts-include-dirs` (array): DTS file include dir for dtsi resolution, depending on the DTS file content

It is to note that all the `with_` options are not mandatory, while others are.

## meson setup
The first step in meson build is project setup, this will create a specific build directory for the given options. This step also configures the toolchain to use.

Some cross-files describing toolchain configuration are set in `support/meson` directory. More than one cross file can be used if needed.

```console
meson setup [-Doption ...] --cross-file=</path/to/cross/file> <builddir>
```

A typical complete setup of the Sentry kernel can then be, in a standalone mode:

```console
defconfig configs/stm32f429i_disc1_autotest_defconfig
meson setup -Dwith_doc=true -Dwith_tests=true -Ddts=dts/examples/stm32f429i_disc1_autotest.dts -Dconfig=.config --cross-file support/meson/armv7m.ini --cross-file support/meson/cortex-m4.ini builddir
```

## build

Once meson build directory is setup, the build step is as simple as calling ninja.
```console
ninja -C builddir
```

## formal proofness

Sentry kernel formal proofness is supported by Frama-C framework. It is based on the
analysis of the libsentry sources, which include all the kernel drivers,
services, etc. except the kernel entrypoint.

EVA and RTE Frama-C plugins are used in order to validate that the kernel sources do not hold any run-time errors nor undefined behavior in the
overall coverage kernel code (approx. 98%, exluding some defensive unreachable code blocks and assembly calls).

In the same way, WP plugin is used in order to validate the correctness of some subparts of the Sentry kernel. The goal here is to validate that the attended behavior
and border effects match the specifications. The way Frama-C analysis is made is designed in order to allow composition (separated per-module formal proofness in
order to demonstrate the correctness of each module interface, while proving a module is made considering external interfaces specification as valid by hypothesis).

**INFO**: the Frama-C framework requires at least Frama-C Cobalt (27), with why3 and cvc4. Meson check that they are installed on the system.

Frama-C targets are hosted in the `proof` directory and are activable using
the `with_proof` option:

```console
meson setup -Dwith_proof=true [...]
```

It can be directly used with the cross configuration, as frama-C only preprocess the sources and then natively parse the C code into its own AST
in order to analyse the source correctness.

FramaC execution is controled through the meson test framework (see tests chapter) and thus is directly accessible through the test command.
All Frama-C tests are a part of the same suite denoted proof. If both proofs and tests are enabled in the very same time, the proof tests can
then be called separatelly by calling only the proof suite.

FramaC tests can be listed using:

```console
$ meson test -C builddir/ --list
sentry-kernel:proof / frama-C-parsing
sentry-kernel:proof / frama-c-eva-entrypoint
sentry-kernel:proof / frama-C-eva-handler-systick
sentry-kernel:proof / frama-c-eva-handler-svc
sentry-kernel:proof / frama-c-eva-zlib
sentry-kernel:proof / frama-C-eva-handler-systick-redalarm
sentry-kernel:proof / frama-c-eva-handler-svc-redalarm
sentry-kernel:proof / frama-c-eva-zlib-redalarm
[...]
```

Each Frama-C execution is stored in a dedicated build directory that hold all usual files such as session file, red alarms, flamgraph and so on,
that allows various post-processing, such as results analysis or Frama-C tools usage such as `ivette` or `frama-c-gui`.

**Rust UAPI**: As tools like Creusot do not support unsafe, Rust user api proofs are built using Kani model checker.

## tests

### Unit testing

Sentry kernel supports unit testing. This is done using the gtest framework.
Analysis of various components of the Sentry kernel is made by emulating, for each subcomponent, the ecosystem it needs in order to simulate the target.
For e.g., the EXTI driver is unit-tested using an emulated EXTI device mapped at the very same memory address map as the effective device, so that the device driver do not need any modifiacations while tested.

Other non-HW related components are tested for their expected behavior, in multiple nominal and borderline cases.

Enabling the test suite is made by activating the tests at setup time:

```console
meson setup -Dwith_tests=true [...]
```

The test framework is based on multiple test suites. The suite names can be listed using the standard `meson test` target:

```console
meson test -C <builddir> --list
sentry-kernel:ut-utils / io
sentry-kernel:ut-utils / bits
sentry-kernel:ut-bsp / exti
```

Each test suite (or even test) can be executed independently if needed:

```console
meson test -C <builddir> --suite ut-utils
[...]
```

### Pre-integration tests with autotest

Sentry support a special applications named autotest (see concepts) that is built in autotest mode in order to execute and validate the
overall Sentry UAPI for efficient performance and anti-regression testing.

When build in autotest mode, the build system generate a dedicated `firmware.hex` file, in which Sentry kernel automatically load and
start the autotest application.
Autotest results can be manually read from serial output, or can be
parsed, generating a full report using **robotframework**. The robot files are written in the `tools/robot` subdir and can be directly called by robotframework, generating a complete report.

When installed, the kernel build system install target deploy the robot files in the `$datadir/robotframework` directory

In order to support example robot files, robotframework-pyocd>=0.2.0 and robotframework-pyserial>=1.2.0 python packages are required.
A typical usage of robot files of the kernel would be, considering the following `pyocd list` content:

```console
pyocd list
  #   Probe/Board       Unique ID                  Target
---------------------------------------------------------------------
  0   STLINK-V3         004300483232510239353236   ✔︎ stm32u5a5zjtxq
      NUCLEO-U5A5ZJ-Q

  1   STM32 STLink      0671FF575251717867205336   ✔︎ stm32f429zitx
      DISCO-F429Z
```

```console
robot --variable FIRMWARE_FILE:builddir/firmware.hex --variable PROBE_UID:004300483232510239353236 -d results ./tools/robot/sentry-autotest.robot
```

All results (report and logs) are then deployed in the results local directory.

## Documentation

Sentry documentation is written in the `doc/` subdirectory.
It can be build if the `with_doc` flag is set to true.

There are multiple doc types:

   * concepts: Overall Sentry concepts definition, and high level documentation, targetting the user or application developer
   * internals: Sentry internal code hierarchy, mostly built using doxygen. This doc is for kernel developers
   * mandb: Sentry UAPI manuals, in groff (man) format, so that it can be used with the `man` utitily

The ninja targets associated to these documentations are `doc-concepts` (`doc-concepts-pdf` for PDF generation), `doc-internals` and `mandb`.

Generated documentation is in the `$BUILDDIR/doc` directory, and are also deployed in `/usr/share/doc` in case of the usage of the `install` target.

More information about the various concepts of the Sentry-kernel and its build system can be found in the `concepts` documentation.
