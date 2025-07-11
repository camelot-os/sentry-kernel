sys_get_dma_handle
""""""""""""""""""
.. _uapi_get_dma_stream_handle:

**API definition**

   .. code-block:: c
      :caption: C UAPI for get_dma_stream_handle syscall

      enum Status __sys_get_dma_stream_handle(uint32_t label);

**Usage**

   In Sentry, all DMA streams are uniquely identified by ther handle. At bootup,
   the user-space task only holds the DMA stream label, as defined in the `sentry,label`
   attribute of the DMA stream in the project ``dts`` file. This label is unique to
   the system.

   DMA streams can only be manipulated through their handle, which must be requested by
   the owner task. The DMA handle values are forged at bootup and valid until next reboot.

   .. note::
       the DMA stream value is stored in the device tree file. This value is a 8 bits unsigned
       identifier. There must not have collision between DMA identifiers, but other objects identifiers
       are considered separately

   .. code-block:: C
      :linenos:
      :caption: sample bare usage of sys_get_dma_handle

      uint32_t my_stream_label = 0x42;
      dmah_t my_stream_handle;
      if (__sys_get_dma_stream_handle(my_dma_label) != STATUS_OK) {
         // [...]
      }
      copy_from_kernel(&my_dma_handle, sizeof(devh_t));

**Required capability**

   Like all other DMA-related syscalls, this syscall needs the calling task to hold the CAP_DEV_DMA capability.

**Return values**

   * STATUS_INVALID if the handle do not exist or can't be assigned
   * STATUS_DENIED if the stream is not owned or the CAP_DEV_DMA is not hold by the task
   * STATUS_OK if the handle is properly retuned to the calling job

**See also**

    `sys_dma_assign_stream` (2), `sys_dma_unassign_stream` (2), `sys_dma_start_stream` (2), `sys_dma_suspend_stream` (2),
    `sys_get_dma_stream_handle` (2)
