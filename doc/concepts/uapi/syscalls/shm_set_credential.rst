sys_shm_set_credential
""""""""""""""""""""""
.. _uapi_shm_set_crendential:

**API definition**

   .. code-block:: c
      :caption: C UAPI for shm_set_crendential syscall

      enum Status __sys_get_shm_handle(shmh_t shm, taskh_t target, uint32_t perms);

**Usage**

   In Sentry, as explained in :ref:`SHM model definition chapter <shm_principles>`, a shared memory
   hold credential for its owner and user task.

   These credentials need to be set at bootup by the owner task. Only the owner task is allowed to
   set credentials of both itself and any other user task.

   Setting credentials is made using the `shm_set_credential()` syscall, targetting a given task handle.

   The task handle can be:

      * the owner itself, meaning that the configured credential is associated with the owner
      * another task handle, meaning that the configured credential is associated with another task

   If the target task is declared for the first time, it become the user task with which the SHM
   is shared.

   An owner can't set credential for a target that currently maps the SHM. This means that credential
   must be set for a target that currently do not map it. This is required to keep coherency between the
   currently mapped ressources and the kernel configuration.

   If not mapped and the target task hande changes, the previously set job associated with the previous
   task handle with which the shared memory is shared can't map the SHM any more.

   The following credential flags exist:

      * SHM_PERMISSION_MAP: the shared memory is mappable by the credential target task
      * SHM_PERMISSION_READ: the shared memory is readable when mapped. On MCU devices, it is always true
      * SHM_PERMISSION_WRITE: the shared memory is writeable when mapped
      * SHM_PERMISSION_TRANSFER: the shared memory user can be transferable to another task

   These flags are ORed so that multiple flags can be set if needed.

   It is to note that the SHM_PERMISSION_MAP is ignored if the `sentry,no-map` attribute in the device tree is set
   (see :ref:`SHM general description <shm_principles>` of Sentry concept, for more information).

   .. code-block:: C
      :linenos:
      :caption: sample bare usage of sys_shm__set_credential

      uint32_t my_shm_label=0xf00UL;
      taskh_t myself;
      if (__sys_get_task_handle(myself_label) != STATUS_OK) {
         // [...]
      }
      copy_from_kernel(&myself, sizeof(taskh_t));
      if (__sys_get_shm_handle(my_shm_label) != STATUS_OK) {
         // [...]
      }
      copy_from_kernel(&my_shm_handle, sizeof(shmh_t));

      __sys_shm_set_credential(my_shm_handle, myself, SHM_PERMISSION_MAP | SHM_PERMISSION_WRITE);

**Required capability**

   None.

**Return values**

   * STATUS_INVALID if the SHM do not exist, target do not exist or is not owned or used by the calling task
   * STATUS_DENIED if the calling task is the user, not the owner
   * STATUS_BUSY if the target associated with the credential has the SHM mapped
   * STATUS_OK
