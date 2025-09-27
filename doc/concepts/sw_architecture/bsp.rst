Hardware support in Sentry
--------------------------

.. _bsp:

Basics about HAL
^^^^^^^^^^^^^^^^

Sentry HAL is built around two main blocks, including a set of *device drivers*
and a *platform support* component, corresponding to the board and the architecture
support package of the micro-kernel.

As this is a micro-kernel, these two components are quite small, reduced to what
is required to bootup, secure and spawn the userspace tasks.


Adding a new board
------------------

A new board in Sentry, while the board SoC is supported, should not require any
source modification. The board configuration and pinout should be fully defined
through the board device tree, and thus being considered as an input information for
the kernel while the corresponding SoC required platform and device drivers are
supported.

.. note::

  Using full dts-based board support allows to keep the very same Sentry git tag or
  source distribution (dist target) for board evolution in a given project, ensuring that
  no modification has been made to a source that have passed quality gate or certifications

Adding a new SoC
----------------

Adding a new SoC is a work that may require more or less work depending on the level
of platform related modifications. For a new SoC for which all the platform related
part is already supported (e.g. adding a new armv7m SoC), only missing drivers or
upgrade to incomplete drivers is required.


Update SVD database
^^^^^^^^^^^^^^^^^^^

Sentry is using SVD files in order to forge SoC-related informations such as IRQ list and
per-IP registers definition. The SVD database is hosted in a `decicated repository <https://github.com/camelot-os/kadoc>`_.
Adding a SVD file (or a set of files) is done through a dedicated pull request on this repo by:

   * adding the SVD file(s) in the corresponding `svd/` subdir
   * update the `meson.build` file in the very same directory by adding the SVD file(s) to the
     list

This update is relatively basic and easy to create.

.. note::
   If a new manufacturer is added, please create a new directory with the same layout as the
   existing `st` subdir, and add it to the parent `meson.build` directory


Adding the manufacturer dtsi file
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In the same way SVD files are used to forge the SoC source files for CMSIS and driver related
registers mapping, dtsi files are used so that all devices mapping, familly and featureset,
as generically defined for all OSes.

The dtsi files are stored in a dtsi database hosted in a `decicated repository <https://github.com/camelot-os/camelot-devicetree>`_.
There are already a lot of dtsi files, hosted in this repository's `dts/` subdir. In the very same
way SVD are added, dts files can be simply included in the corresponding subdir. There is no need
in that case to update any of the `meson.build` files though.

.. note::
   DTSI files can be found, for example, in the Zephyr project sources. Please do not modify any of the
   copyright headers. The licensing model of the dtsi file must be kept. By now, dtsi files are using Apache-2.0
   licensing model

Adding a new SoC BSP in Sentry sources
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Such a port should only impact two main elements:

   * the `kernel/src/arch/asm-cortex-m/Kconfig` file, that describes, for each SoC, the corresponding properties.
     When adding a new SoC family (e.g. STM32L4 family), the following entry needs to be added so that SoC properties are
     triggered:

     .. codeblocks::
      config SOC_SUBFAMILY_STM32L4
        bool
        select ARCH_ARM_CORTEX_M4
        select SOC_FAMILY_STM32
        select HAS_FPU
        select HAS_FPU_VFPV4
        select HAS_MPU
        select HAS_MPU_PMSA_V7
        select HAS_DCACHE
        select HAS_ICACHE
        select HAS_RNG
        help
          STM32L4 family is based on Cortex-M4 with FPU and PMSAv7 MPU with low power features

     In the same way, the `ARCH_SOCNAME` must be updated with the new SoC. Don't hesitate to take a look at the Kconfig
     file to understand the principle.

   * the `kernel/src/drivers` subdir. The Sentry-private driver API, exposed in `include/bsp` and used by managers,
     should not be modified as this API has no device-specific element.
     By modifying or adding only corresponding driver, the impact of such a modification should
     not generate border effects in others kernel parts, including managers and syscalls, and should
     not require any modification of unit tests other than including new, new SoC specific, tests.
     Adding a new device driver should be made in the same way Linux drivers behave: for required devices
     (u(s)art, clock, exti, gpio, rng (when present), dma and sysconfig), there is already a set of supported
     devices. Each driver hold three types of sources:

        * family generic code (e.g. `stm32-rcc.c`) that should work for an entire family
        * subfamily generic code (e.g. `stm32u5-rcc.c`) that work for a given subfamily, added alongside the family level code
        * in some rare case, the model-specific code that works only for a given SoC, to be added alongside others

     Once written, the source selector needs to be updated in the driver's directory `meson.build` file. This is easily made
     by simply adding such a typical configuration:

     .. codeblocks::
        if kconfig_data.get('CONFIG_SOC_SUBFAMILY_STM32U5', 0) == 1
          bsp_clk_source_set.add(myfile.c)
        endif

     The CONFIG value should basically correspond to the one added in the Kconfig file. Use the FAMILY/SUBFAMILY granularity
     depending on the level of specificity of the device.

Once done, it should be possible to define a dts file and a defconfig file for that SoC. See the `configs` and `dts` directories
for typical examples. config files are built as `defconfig` content, while the dts file can include the previously added dtsi file
easily in the same way already existing dts files exists.

.. note::
  When adding a new SoC, please at least add default `defconfig` and `dts` file for that SoC so that the CI can build a kernel
  debug and autotest profile for it

.. note::
  If a proprietary board is required, the corresponding `dts` and `config` files can of course be kept separately, in a
  proprietary repository if needed, using the `dts=` and `config=` arguments

Adding a new architecture
-------------------------

Adding a new architecture correspond to the addition of a new directory in the `src/arch`
subdir, associated to `include/sentry/arch/`. This new directory add all the new hardware
specific implementations. The hardware dispatcher, that use the complier's variables to
know which target architecture is used, need to be updated in `include/sentry/arch/asm-genric`
directory.

.. note::

    `include/sentry/arch/asm-genric` directory is used as a trampoline to hardware specific
    headers. Headers in that directory are dispatcher to correct hardware subdirectory headers
    and may, for some of them, hold some generic code.

    Headers out of `arch/asm-*` directories are headers for components that have no link with
    hardware related features.
