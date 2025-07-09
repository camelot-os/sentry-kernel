.. _userspace_devices:
About user devices
------------------

Device list generation and kernel storage
"""""""""""""""""""""""""""""""""""""""""

A word about project device tree usage
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The Sentry kernel hold a list of the active devices of the project that is
forged using the project's device tree. This is a useful helper as by doing
that, only active devices are stored in the Sentry kernel device list,
seen as a whitelist.

When a Sentry-based project modify its device tree to add or remove a device,
or update a board reference, modying some device's pinmux configuration, the
kernel device listing and associated configuration is automatically regenerated.

.. note::
    an active device is a device declared with `status = okay` in the
    device tree, meaning that it can be used at runtime. Others are ignored

The kernel device listing
~~~~~~~~~~~~~~~~~~~~~~~~~

The kernel list, generated using the device tree file, hold for each device
the following elements:

   * **devh_t**: the device handle, which uniquely identify the device on the
     system. This handle is also used when forging the corresponding _userspace
     driver metadata that include the very same field. This opaque is used in
     order to share the device identification between kernelspace and userspace.

   * **addresses**: base address and size, used for memory mapping. These informations
     are known by the userspace driver even if never directly manipulated, as
     userspace driver registers address are generated using SVD file. When using
     the *Map* UAPI, the *devh_t* is enough to map and clock the device.

   * **clocking**: this part is only hold by the kernel and correspond to the device
     clocking requirements, as defined in the device tree.

   * **capability**: Each user device is associated to a capability. This capability
     must be owned by the requiring task to manipulate it. More about device capabilities
     assignation is described in :ref:`auto-assignation of device capability <capa_deb_assign>` chapter.

   * **interrupts**: If the device holds interrupt lines, they are declared here,
     which allows to move between `IRQn` and `devh_t`.

   * **IOs**: If the device has configured I/Os (device tree's pinmux configuration), it is
     fully declared here. The complete I/0 configuration for the target board and SoC is
     stored directly in the device data thanks to the dt-bindings. This allows to fully configure
     I/O ports for the device when required.

.. note::
    see `Linux kernel Bindings documentation <https://elixir.bootlin.com/linux/latest/source/Documentation/devicetree/bindings>`_
    for more information on what is a binding


Auto-assignation of device capability
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. _capa_deb_assign:

Devices :ref:`capabilities <capabilities>` is a subset of all Sentry capabilities that correspond to hardware IPs.
They are associated to the security impact of the device on the system, and are device family-based.

As it possible, for all MCU embedded devices, to associate a familly, the capability association can be made
automatically. This is the direct consequence of the device tree usage, which already use the device `compatible`
field that define a device family model.

For example, if we consider buses, we typically find the follwing set in the device tree (e.g. with a stm32 dtsi):

.. code-block:: dts
  :linenos:
  :emphasize-lines: 2,6,10,14

   usart3: serial@40004800 {
      compatible = "st,stm32-usart", "st,stm32-uart";
      [...]
   };
   spi3: spi@40003c00 {
      compatible = "st,stm32-spi";
      [...]
   };
   can1: can@40006400 {
      compatible = "st,stm32-bxcan";
      [...]
   };
   usbotg_hs: usb@40040000 {
      compatible = "st,stm32-otghs";
      [...]
  };

These devices are of the following standard types:

   * `usart`, `uart`: serial ports
   * `spi`: spi buses
   * `bxcan`: CAN buses
   * `otghs`: USB High speed with on-the-go (OTG) capability

If we assign to this set of standard types the capability `CAP_DEV_BUSES`, then it is possible
to autoatically assign capability to each device, based on its compatible field(s).
This allows Sentry kernel to forge a device list with a per-device capability automatically.

This is done for all devices capabilities, using a device family set to capability inclusion
mechanism. The following device capabilities exist and are required by the requester in
order to allow the corresponding device usage:

   * **CAP_DEV_BUSES**: buses, such as u(s)art, spi, i2c, USB, CAN, and so on
   * **CAP_DEV_IO**: used for direct I/O usage (pure GPIO pin control, such as LED, external interrupt, etc.)
   * **CAP_DEV_DMA**: DMA controlers, such as dma, dma2d
   * **CAP_DEV_ANALOG**: dac, adc, etc.
   * **CAP_DEV_TIMER**: hardware timers
   * **CAP_DEV_STORAGE**: mmio, sdmmc, etc.
   * **CAP_DEV_CRYPTO**: hw cryptographic device (aes, hmac, etc.)
   * **CAP_DEV_CLOCK**: RTC clock, etc.
   * **CAP_DEV_POWER**: power control management
   * **CAP_DEV_NEURAL**: neural coprocessor

Some post-generation checks are required:

   * A device **must** have a CAP_DEV capability
   * A device **must** have exactly one capability

As capability is forged at build time, the device list can be directly used in order to
check that the requester is able to access the device in a capability-based mode.

(Un)mapping devices
"""""""""""""""""""

Mapping and unmapping device is a natural manipulation as the memory ressources may
be restricted due to MPU region number constraints.
A device is never automatically mapped in the job memory area, leaving the map
request under the control of the userspace algorithm.
On the other side, unmapping is not always required, and mapped ressources are
kept between context switches.

The userspace code do not have access to the clocking part of the device. Device
clocking is made the first time it is mapped into the job memory area.

.. note::
  mapping and unmapping devices is done using the `devh_t` handle only, which
  is enough to identify uniquely the device on the platform.

Linking IRQ with its owner
""""""""""""""""""""""""""

Devices usually have IRQ assigned to it. If the userspace activate the device's
interrupts in the device register configuration, the kernel will return IRQ events
through the unified events listening syscall, as defined in the :ref:`UAPI events <events>`
chapter.

The link between IRQ and device is already known through the device list forged
from the device tree, as IRQ assignation is declared in the dts file.

.. code-block:: dts
  :linenos:
  :emphasize-lines: 4

  uart5: serial@40005000 {
          compatible = "st,stm32-uart";
          [...]
          interrupts = <53 0>;
          status = "disabled";
  };

It is then easy to get back the `devh_t` handle from the IRQ number, and then The
task owner from the `devh_t` handle. The IRQ is then pushed as a `irqh_t` event
in the job input IRQ queue, which may, depending on the current job state, activate
the scheduling of the job.

.. warning::
  Jobs that are blocked by the transmission of an IPC to another job are not awoken.
  They will be awoken by the IPC reception in the other job, and will receive the
  `irqh_t` as soon as they come back to the `sys_waitforevent()` blocking point.
