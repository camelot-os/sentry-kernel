Devicetree integration
------------------------

Sentry use `Devicetree Specification <ttps://www.devicetree.org/specifications/>`_ for hardware
description and configuration. Dts [#]_ file is preprocessed at build time and used to
generate code according to configuration. Dts file dts include dir (for fragments and bindings
resolution) have to be passed at project configure time, see
:ref:`Bootstraping Sentry build<Bootstraping Sentry build>` section.

.. [#] Device Tree Source


CamelotOS/Sentry requires custom nodes and property to work as expected.

Properties
^^^^^^^^^^

.. _sentry_owner_property:
``sentry,owner`` property
""""""""""""""""""""""""""

This property is an ``u32`` type property used to assign the owner :ref:`task label <Task handle>`
to a the parent node. This property is mandatory for each mappable and/or restricted node
as :ref:`userspace devices<userspace_devices>`, :ref:`shared memories <shm_principles>` and
dma buffers.

.. code-block:: dts
  :linenos:
  :emphasize-lines: 5

  /{
    ...
    some_nodelabel: name@address {
        ...
        sentry,owner = <0xbabe>;
        ...
      };
  };

``chosen`` node
^^^^^^^^^^^^^^^

``sentry,debug_stdout`` property
""""""""""""""""""""""""""""""""
This property defines the device to use as standard output use in debug mode if configured.
..
    Add a reference to config here

- type: ``phandle``
- parent: ``chosen``

.. code-block:: dts
  :linenos:
  :emphasize-lines: 3

  /{
      chosen {
          sentry,debug_stdout = <&usart1>;
      }
  };



``sentry,kernelram_section`` property
"""""""""""""""""""""""""""""""""""""

Reference to the kernel ram reserved memory region.

- type: ``phandle``
- parent: ``chosen``

.. note::
    This property is mandatory


``sentry,idleram_section`` property
"""""""""""""""""""""""""""""""""""

Reference to the idle task ram reserved memory region.

- type: ``phandle``
- parent: ``chosen``

.. note::
    This property is mandatory

``sentry,kernelcode_section`` property
""""""""""""""""""""""""""""""""""""""

Reference to the kernel code reserved memory region.

- type: ``phandle``
- parent: ``chosen``

.. note::
    This property is mandatory

``sentry,idlecode_section`` property
""""""""""""""""""""""""""""""""""""

Reference to the idle task code reserved memory region.

- type: ``phandle``
- parent: ``chosen``

.. note::
    This property is mandatory

``sentry,autotestram_section`` property
"""""""""""""""""""""""""""""""""""""""

Reference to the autotest task ram reserved memory region.

- type: ``phandle``
- parent: ``chosen``

.. note::
    Required while build in autotest mode

..
    Add ref to autotest mode

``sentry,autotestcode_section`` property
""""""""""""""""""""""""""""""""""""""""

Reference to the autotest task code reserved memory region.

- type: ``phandle``
- parent: ``chosen``

.. note::
    Required while build in autotest mode
..
    Add ref to autotest mode

``sentry,rng`` property
"""""""""""""""""""""""
TBD

..
    Not implemented yet, will be, likely, a phandle to a rng type device

``reserved-memory`` node
^^^^^^^^^^^^^^^^^^^^^^^^

``reserved-memory`` is the node holding memory region reserved for a specific usage. This
could be kernel, idle task or user tasks code/ram region, shared memory or, dma buffers.
Each child node describe one region with the following properties:

 - ``reg``: <`base_address` `size`> (mandatory)
 - ``dma-pool``: boolean, this region can be used as dma-pool.
 - ``sentry,shm``: boolean, can be use as shared memory, this property requires sentry,label and sentry,owner property to be defined
 - ``sentry,label``: memory region label (used by user space to get internal opaque handler)
 - ``sentry,owner``: see :ref:`sentry_owner_property` section.
 - ``sentry,no-map``: prevent region to be mapped by sentry kernel.

.. important::
    [kernel/idle/autotest/tasks]_code/ram label are reserved and mandatory in order to declare,
    respectively, kernel, idle task, autotest task and user defined tasks memory region.
    `autotest`` and `tasks` are mutually exclusive as there is no user tasks in autotest mode.
    All user tasks are relocated at project build time in the configured region.
    For those regions, only ``reg`` property is required, all others are ignored.

.. warning::
    reserved memory regions must comply with target MPU alignment requirements.

.. code-block:: dts
  :linenos:
  :emphasize-lines: 5,9,13,17,21,25

    reserved-memory {
        #address-cells = <1>;
        #size-cells = <1>;

        kernel_code: memory@8000000 {
            reg = <0x8000000 0x8000>;
            compatible = "sentry,memory-pool";
        };
        idle_code: memory@8008000 {
            reg = <0x8008000 0x300>;
            compatible = "sentry,memory-pool";
        };
        kernel_ram: memory@20000000 {
            reg = <0x20000000 0x2000>;
            compatible = "sentry,memory-pool";
        };
        idle_ram: memory@20004000 {
            reg = <0x20004000 0x200>;
            compatible = "sentry,memory-pool";
        };
        tasks_code: memory@0800a000 {
            reg = <0x0800a000 0x200000>;
            compatible = "sentry,memory-pool";
        };
        tasks_ram: memory@20008000 {
            reg = <0x20008000 0x280000>;
            compatible = "sentry,memory-pool";
        };
    };
