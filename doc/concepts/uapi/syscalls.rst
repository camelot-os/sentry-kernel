Syscalls
--------

About basics
^^^^^^^^^^^^

Sentry UAPI is implemented in Rust. In order to ensure compatibility with
both Rust and C worlds, the UAPI specification is made using `extern C`
external interface specification and types, and the crate defintion is
automatically exported to C headers using `cbindgen`.

This allows a single root of trust for all UAPI definition, for both languages,
in our case using a Rust definition that ensure struct typing usage.

The UAPI is design using the following:

   * a `systypes` package, that define all Sentry types shared with userspace
   * a `uapi` package, that hold the UAPI implementation in rust, depending on `systypes`

In the kernel counter part:

   * a `sysgate` package, that define all the kernel syscall implementation, and
     also depend on `systypes`


The UAPI description is made for C usage of the UAPI. For Rust definition, please
refer to the Rust generated documentation.

.. index::
  single: UAPI; syscalls
  single: UAPI; syscall definition



Syscall definition
^^^^^^^^^^^^^^^^^^

.. index::
  single: sys_alarm; definition
  single: sys_alarm; usage
.. include:: syscalls/alarm.rst

.. index::
  single: sys_dma_assign_stream; definition
  single: sys_dma_assign_stream; usage
.. include:: syscalls/dma_assign_stream.rst

.. index::
  single: sys_dma_resume_stream; definition
  single: sys_dma_resume_stream; usage
.. include:: syscalls/dma_resume_stream.rst

.. index::
  single: sys_dma_start_stream; definition
  single: sys_dma_start_stream; usage
.. include:: syscalls/dma_start_stream.rst

.. index::
  single: sys_dma_suspend_stream; definition
  single: sys_dma_suspend_stream; usage
.. include:: syscalls/dma_suspend_stream.rst

.. index::
  single: sys_dma_unassign_stream; definition
  single: sys_dma_unassign_stream; usage
.. include:: syscalls/dma_unassign_stream.rst

.. index::
  single: sys_exit; definition
  single: sys_exit; usage
.. include:: syscalls/exit.rst

.. index::
  single: sys_get_dev_handle; definition
  single: sys_get_dev_handle; usage
.. include:: syscalls/get_dev_handle.rst

.. index::
  single: sys_get_shm_handle; definition
  single: sys_get_shm_handle; usage
.. include:: syscalls/get_shm_handle.rst

.. index::
  single: sys_get_dma_handle; definition
  single: sys_get_dma_handle; usage
.. include:: syscalls/get_dma_stream_handle.rst

.. index::
  single: sys_get_random; definition
  single: sys_get_random; usage
.. include:: syscalls/get_random.rst

.. index::
  single: sys_get_task_handle; definition
  single: sys_get_task_handle; usage
.. include:: syscalls/get_task_handle.rst

.. index::
  single: sys_gpio_get; definition
  single: sys_gpio_get; usage
.. include:: syscalls/gpio_get.rst

.. index::
  single: sys_gpio_reset; definition
  single: sys_gpio_reset; usage
.. include:: syscalls/gpio_reset.rst

.. index::
  single: sys_gpio_set; definition
  single: sys_gpio_set; usage
.. include:: syscalls/gpio_set.rst

.. index::
  single: sys_gpio_toggle; definition
  single: sys_gpio_toggle; usage
.. include:: syscalls/gpio_toggle.rst

.. index::
  single: sys_has_respawned; definition
  single: sys_has_respawned; usage
.. include:: syscalls/has_respawned.rst

.. index::
  single: sys_irq_acknowledge; definition
  single: sys_irq_acknowledge; usage
.. include:: syscalls/irq_acknowledge.rst

.. index::
  single: sys_irq_enable; definition
  single: sys_irq_enable; usage
.. include:: syscalls/irq_enable.rst

.. index::
  single: sys_irq_disable; definition
  single: sys_irq_disable; usage
.. include:: syscalls/irq_disable.rst

.. index::
  single: sys_log; definition
  single: sys_log; usage
.. include:: syscalls/log.rst

.. index::
  single: sys_map_dev; definition
  single: sys_map_dev; usage
  single: sys_unmap_dev; definition
  single: sys_unmap_dev; usage
.. include:: syscalls/map.rst

.. index::
  single: sys_map_shm; definition
  single: sys_map_shm; usage
.. include:: syscalls/shm_map.rst

.. index::
  single: sys_unmap_shm; definition
  single: sys_unmap_shm; usage
.. include:: syscalls/shm_unmap.rst

.. index::
  single: sys_pm_clock_set; definition
  single: sys_pm_clock_set; usage
.. include:: syscalls/pm_clock_set.rst

.. index::
  single: sys_send_ipc; definition
  single: sys_send_ipc; usage
.. include:: syscalls/send_ipc.rst

.. index::
  single: sys_send_signal; definition
  single: sys_send_signal; usage
.. include:: syscalls/send_signal.rst

.. index::
  single: sys_shm_set_credential; definition
  single: sys_shm_set_credential; usage
.. include:: syscalls/shm_set_credential.rst

.. index::
  single: sys_shm_get_infos; definition
  single: sys_shm_get_infos; usage
.. include:: syscalls/shm_get_infos.rst

.. index::
  single: sys_wait_for_event; definition
  single: sys_wait_for_event; usage
.. include:: syscalls/waitforevent.rst
