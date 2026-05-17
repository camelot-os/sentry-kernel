sys_has_respawned
"""""""""""""""""

**API definition**

   .. code-block:: c
      :caption: C UAPI for has_respawned syscall

      enum Status __sys_has_respawned(void);

**Usage**

   Check if a respawning event has occurred for the current task.

   This syscall is useful for tasks that are configured to be restarted on termination, using the
   CONFIG_TASK_EXIT_RESTART configuration flag.

   .. code-block:: C
      :linenos:
      :caption: sample bare usage of sys_has_respawned

      if (__sys_has_respawned() == STATUS_OK) {
         // respawn event has occurred, the task has been restarted by the kernel
      }

**Required capability**

   None.

**Return values**

   * STATUS_OK: respawn event has occurred, the task has been restarted by the kernel
   * STATUS_AGAIN: no respawn event has occurred by now

Note that there is no respawn counter nor timing information on when the respawn event has occurred.
The task can only check if a respawn event has occurred since the last time it checked,
or since the task initialization if it never checked before.
