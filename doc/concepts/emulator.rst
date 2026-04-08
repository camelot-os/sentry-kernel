.. _emulator:

Sentry Emulator
---------------

.. index::
   single: emulator; sentry-emulator
   single: POSIX; uapi backend


Why an emulator?
^^^^^^^^^^^^^^^^

The Sentry kernel targets embedded microcontrollers (ARM Cortex-M, etc.), which
are ``no_std`` platforms with no host operating system.  Developing and
validating Sentry applications on real hardware involves cross-compilation and
flashing cycles that slow iteration significantly.

The Sentry emulator allows a Sentry application — written against the
``sentry-uapi`` crate — to run directly on a GNU/Linux x86_64 system *without
any embedded hardware*.  It intercepts Sentry system calls and emulates them at
user level, providing:

* a fast on-host development environment;
* the ability to write automated integration tests covering full end-to-end
  application behaviour (IPC, signals, alarms, log, etc.);
* support for continuous integration pipelines that have no access to real
  embedded hardware.


How the emulator works and how ``sentry-uapi`` integrates with it
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: gRPC; emulator
   single: protobuf; emulator

General architecture
""""""""""""""""""""

The emulator is a Python daemon that exposes a gRPC service on
``127.0.0.1:44044`` (configurable).  The communication between an application
and the daemon is based on the Protobuf protocol defined under
``tools/sentry-emulator/proto/``.

When an application compiled in POSIX mode
(``--target x86_64-unknown-linux-gnu`` with the ``std`` feature) issues a Sentry
system call, the POSIX backend of the ``sentry-uapi`` crate
(``uapi/src/posix.rs``) intercepts the call and:

1. serialises the syscall name, its arguments, and the exchange buffer into a
   Protobuf ``DispatchRequest`` message;
2. sends that message to the daemon over gRPC (``Dispatch`` RPC);
3. waits for the ``DispatchResponse`` that carries the Sentry status code and,
   when applicable, the updated contents of the exchange buffer.

The Python daemon receives requests, validates them, traces them in its logs,
and executes the corresponding emulation logic (blocking IPC, signal delivery,
alarm, etc.).  Each started application is given a unique *context* identified
by its **label** (a ``u32`` integer).

.. code-block:: none
   :caption: Syscall flow through the emulator

   Rust application
          │
          │  using sentry-uapi crate
          ▼
    sentry-uapi Rust crate (in native GNU/Linux mode)
          │
          │  via sentry-uapi gRPC backend (tonic/gRPC)
          ▼
   sentry-emulator daemon (Python / gRPC)
          │
          │  DispatchRequest { syscall, args, label, payload }
          ▼
   EmulatorServicer.Dispatch()
          │
          │  emulation logic
          ▼
   DispatchResponse { status, detail, payload }
          │
          ▼
   Rust application (syscall result)

``sentry-uapi`` integration
""""""""""""""""""""""""""""

The POSIX backend is activated automatically when the crate is compiled for the
``x86_64-unknown-linux-gnu`` target with the ``std`` feature.  Connection
parameters are read from the environment at application startup:

.. list-table::
   :header-rows: 1
   :widths: 30 20 50

   * - Environment variable
     - Default value
     - Purpose
   * - ``SENTRY_EMULATOR_HOST``
     - ``127.0.0.1``
     - Daemon listening address.
   * - ``SENTRY_EMULATOR_PORT``
     - ``44044``
     - gRPC service port.
   * - ``SENTRY_APP_LABEL``
     - ``0``
     - Application label registered in the emulator.

These variables are set automatically by the daemon when it launches
applications via the ``--start`` option.

Local syscalls that do not involve exchange with other tasks
(``sched_yield``, ``exit``, etc.) are handled locally by the POSIX backend
without reaching the daemon.


Building and installing the emulator as a Python package
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: installation; Python emulator

The emulator is a standard Python package (``camelot.sentry-emulator``)
managed with ``setuptools`` and ``setuptools-scm``.

Manual build
""""""""""""

From the ``tools/sentry-emulator/`` directory:

.. code-block:: sh

   # Build the wheel and the sdist
   python -m build

Artifacts (``*.whl`` and ``*.tar.gz``) are written to ``dist/``.

Installing into a virtual environment
""""""""""""""""""""""""""""""""""""""

.. code-block:: sh

   python -m venv .venv
   source .venv/bin/activate
   pip install dist/camelot.sentry_emulator-*.whl

Once installed, the ``sentry-emulator`` command is available in the venv
``PATH``:

.. code-block:: sh

   sentry-emulator --help

Building via Meson
""""""""""""""""""

The Meson build system integrates the emulator build through the
``sentry-emulator-build`` custom target.  It is triggered automatically during
the main build (``build_by_default: true``) and writes artifacts to:

.. code-block:: none

   <builddir>/tools/sentry-emulator/dist/


Testing the emulator via Meson and the Rust sample applications
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: tests; emulator
   single: sample-app-one; sample-app-two

The two Rust sample applications
""""""""""""""""""""""""""""""""""

The ``tools/sentry-emulator/sample-rust-app/`` sub-project produces two
binaries, ``sample-app-one`` and ``sample-app-two``, that together form a
complete end-to-end validation scenario for the emulator:

.. list-table::
   :header-rows: 1
   :widths: 20 80

   * - Binary
     - Role
   * - ``sample-app-one``
     - *Sender* — sends a blocking IPC to ``sample-app-two``, then emits a
       signal and exercises the ``alarm``, ``random``, and ``get_cycle``
       syscalls.
   * - ``sample-app-two``
     - *Receiver* — waits for the IPC via ``wait_for_event``, processes the
       payload, handles the incoming signal, then runs the same shared
       verification steps.

Separating sender and receiver allows the set of inter-task communication
primitives (IPC, signals) that form the core of the Sentry execution model to
be tested in isolation.

Building the sample applications
""""""""""""""""""""""""""""""""""

The binaries are compiled automatically by Meson via the
``sentry-emulator-sample-rust-app-build`` target and placed in:

.. code-block:: none

   <builddir>/tools/sentry-emulator/sample-rust-target/debug/sample-app-one
   <builddir>/tools/sentry-emulator/sample-rust-target/debug/sample-app-two

To build them manually:

.. code-block:: sh

   cd tools/sentry-emulator/sample-rust-app
   cargo build

Running end-to-end tests
"""""""""""""""""""""""""

End-to-end tests are marked ``emulator`` in pytest and can be run in several
ways.

With tox (from ``tools/sentry-emulator/``):

.. code-block:: sh

   tox -e emulator

With pytest directly (the sample applications must be built first):

.. code-block:: sh

   pytest -m emulator

The main test (``test_cli_starts_sample_rust_apps_via_start``):

1. checks that both binaries are present in ``builddir``;
2. launches the ``camelot.sentry_emulator`` daemon with
   ``--start sample-app-one,label=7`` and ``--start sample-app-two,label=8``;
3. waits for the daemon to terminate naturally (when all sample applications
   have called ``exit``);
4. asserts that the process return code is ``0``.

.. note::
   If the Rust binaries are not present in ``builddir``, the test is
   automatically skipped (``pytest.skip``) with an explicit message.


Using the emulator with your own applications
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: usage; emulator

Prerequisites
"""""""""""""

* The emulator is installed (via pip or the Meson venv).
* The application is compiled for ``x86_64-unknown-linux-gnu`` with the ``std``
  feature of ``sentry-uapi``.

Minimal example
"""""""""""""""

Assume two applications ``my-task-a`` (label ``10``) and ``my-task-b``
(label ``11``):

.. code-block:: sh

   # Start the emulator and register the two tasks to launch
   sentry-emulator \
       --log-level INFO \
       --start ./target/x86_64-unknown-linux-gnu/debug/my-task-a,label=10 \
       --start ./target/x86_64-unknown-linux-gnu/debug/my-task-b,label=11

The daemon will:

1. start and listen on ``127.0.0.1:44044``;
2. launch ``my-task-a`` and ``my-task-b``, automatically injecting
   ``SENTRY_APP_LABEL``, ``SENTRY_EMULATOR_HOST``, and
   ``SENTRY_EMULATOR_PORT`` into their environment;
3. receive and process Sentry syscalls emitted by both tasks;
4. terminate cleanly once all launched tasks have called ``syscall::exit``.

To run the daemon on its own (without supervised applications), for example
when tests start their own processes, simply omit the ``--start`` options:

.. code-block:: sh

   sentry-emulator --host 127.0.0.1 --port 44044 --log-level DEBUG

Verbosity levels
""""""""""""""""

.. list-table::
   :header-rows: 1
   :widths: 15 85

   * - Level
     - Information traced
   * - ``INFO``
     - Daemon start/stop, application context lifecycle.
   * - ``WARNING``
     - Invalid or malformed requests received by the daemon.
   * - ``ERROR``
     - Invalid CLI arguments, application launch failures.
   * - ``DEBUG``
     - Full detail of every gRPC request/response and task event.
