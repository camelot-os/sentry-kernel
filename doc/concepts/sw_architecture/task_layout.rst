Task layout
-----------

.. _task_layout:

Introduction to generic task layout
"""""""""""""""""""""""""""""""""""

A task is composed, also in a embedded system, of the following main
elements:

   * **text section**: This section hold the task code. This section is the
     only part of the task that is executable. On embedded systems, this
     part is most of the time hold in flash memory as the flash is direct-mapped.

   * **rodata section**: this section hold the variable that are const (i.e. not
     mutable) at build time. It can be canonical strings, or const variables for
     example. This section is mapped read-only, and, in embedded system, kept in
     flash.

   * **data section**: this section hold global variables that are initialized out
     of any blocks, and as such need to be included in the final binary. As these
     variables are mutable, this section need to be copied in volatile memory so that
     the program can upgrade them.

   * **GoT Section**: the Global Offset Table is the section that hold relative
     address resolution mechanism that allow usage of PIC (Position Independent Code)
     executable. At boot time (or at build time in case of build-time address resolution)
     the GoT need to be updated in order to hold the correct symbol offsets so that
     the program properly resolve all its symbol, whatever its position in flash is.
     In Camelot OS, the GoT is updated at build time by the build system positioner.

   * **bss section**: The BSS hold the uninitialized data of a task. This section do
     not require to be stored in the final binary and thus in flash, but must exist in
     the volatile memory so that the task can manipulate its uninitialized variable properly

   * **heap**: when it exists, hold the allocator pool. In Sentry, the allocator is
     fully userspace and under the responsability of the userspace library. Sentry only
     delivers, if needed, an empty space to hold a memory pool. The heap size is defined
     at task configuration time.

   * **stack**: runtime only too, hold the successive frames that define the current
     task context. Also hold the context saving frame when the task is scheduled.

Layout initialization at system startup
"""""""""""""""""""""""""""""""""""""""

Sentry kernel is responsible for initialize the job layout at startup time. For this,
the Sentry kernel do the following:

   * copy got section from flash to RAM
   * copy data section from flash to RAM
   * zeroify SVC-Exchange aread
   * zeroify bss area


The usage of Global Offset Table in Sentry allows support for relocations, which
gives the build system the ability to modify the position of application **after**
the application compilation and link time. This also allows reusability of
fully generic applications ELF files while the Sentry ABI retrocompatibility is
kept (same major version).

The task mapping is done based on the task metadata table forged by the build system
and included in the final firmware binary at a predefined section address.

As the task meatadata table is an external input content for Sentry kernel:

   1. the task metadata table aim to be kept authenticated using HMAC field To
      validate the metadata authenticity

   2. the task metadata ABI compliance is checked using a dedicated 64bit magic field
      that is unique to each project, and shared between the Sentry kernel configuration and
      the build system. This avoid any unvolontary corruption between projects

.. todo::

    add a more complete explanation about task_metadata struct and table

A typical application mapping at boot time is done as defined in the following:

.. figure:: ../_static/figures/task_mapping.png
   :width: 90%
   :alt: task mapping mechanism
   :align: center

   Example of application mapping at boot time

.. note::
    For more information on the way the build system manipulate applications, forge
    metadata information or store metadata in ELF files, see Sentry buid system documentation

Forging and holding task layout
"""""""""""""""""""""""""""""""

The task layout is not also based on the task code and data section, but may also
contain dynamic ressources such as:

   * mappable devices
   * Shared memories

These ressources are voluntary mapped and unmapped by the job during its execution,
and their mapping must be kept uptodate during the overall job lifecycle.

In Sentry, all userspace ressources are considered in the same way as they consumme
a memory mapping. As a consequence, application data and code are also considered as
(required and always mapped) ressources. The full list of ressources is then:

   * task code section in flash
   * task data section in SRAM
   * all mapped device(s)
   * all mapped shared memorie(s)


This context is hold in the task dynamic context, as a layout configuration table that
define the current mapping structure. This table is defined as simply as the
following:

.. table:: Typical Sentry task layout table
   :widths: auto
   :align: center

   +------------------------+
   |  layout                |
   +========================+
   |  task ressource 0      |
   +------------------------+
   |  task ressource 1      |
   +------------------------+
   |  task ressource 2      |
   +------------------------+
   |  task ressource 3      |
   +------------------------+
   |  task ressource 4      |
   +------------------------+
   |  task ressource 5      |
   +------------------------+
   |  task ressource 6      |
   +------------------------+

.. note::
  This example is based on a system that support at most six concurrently mapped userspace
  ressources, including the task code and data section

Task layout is forged successively:

   * at system bootup: the task layout table is initializd as fully invalid, meaning that
     all corresponding regions (for MPU-based devices) are set automatically as invalid

   * at task metadata parsing time: when the task metadata is parsed, the `code` and `data`
     ressources layout are added to the table, these two layouts are properly configured by
     the memory manager given the metadata information, with the help of the arch-specific
     memory support

   * each time a userspace ressource is mapped or unmapped, the corresponding layout entry is
     added or clear to invalid.


After some time, a typical context may be the following:

.. table:: Sentry task configured layout
   :widths: auto
   :align: center

   +------------------------+------------------------+
   |  layout                |  property              |
   +========================+========================+
   |  task code             |  *set at boot*         |
   +------------------------+------------------------+
   |  task data             |  *set at boot*         |
   +------------------------+------------------------+
   |  invalid region        |  *unmapped previously* |
   +------------------------+------------------------+
   |  USB OTG device        |  *mapped*              |
   +------------------------+------------------------+
   |  invalid region        |  *never used*          |
   +------------------------+------------------------+
   |  invalid region        |  *never used*          |
   +------------------------+------------------------+
   |  shared memory 1       |  *mapped*              |
   +------------------------+------------------------+


Increase context switch speed
"""""""""""""""""""""""""""""

On ARM MPU-based systems, the MPU must support region configuration aliases, which allows
parallel mapping of multiple regions in one time. In sentry, the layout table hold an
opaque C type which is made in order to be automatically used by the hardware backend in order
to optimize memory mapping.

.. note::
  for example, on thumbv7m, the usage of `stmia` is typically efficient for such usage. CMSIS headers
  delivers primitives for optimized configuration

To avoid any branches and checks, each time the CPU execute the handler mode:

   * the kernel reduce the task data section to `svc_exchange` section only as soon as the
     task frame as been saved on the current task stack

   * the kernel execute the current handler (systick, syscall, etc.)

   * the kernel fully map the next task context. If a new task has been elected, any potential previously
     mapped ressource (device, shm) is cleared, as all userspace regions are reconfigured.
     If the task is kept the same, the task data section is naturally remapped through the task context map
