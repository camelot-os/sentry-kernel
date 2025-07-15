Basic principles
----------------

.. _proof_basics:

.. index::
    single: Frama-C; integration

About Frama-C
"""""""""""""

Frama-C (see `Frama-C website <https://www.frama-c.com>`_ for more info) is a
suite of tools dedicated to C software analysis.

Frama-C can be used to:

   * demonstrate the absence of Run-Time Error, including, among them, undefined behaviors
   * demonstrate the correctness of a program, meaning that it does what it is required from it, and not only being exempted of RTE

In Sentry, both (noRTE and correctness) analysis are made. Although, including Frama-C in the Kernel
requires some specific considerations.

Frama-C is able to parse C code. In order to help Frama-C plugin with the considered requirements at any step of the program,
the Frama-C framework use a dedicated syntax denoted ACSL.


.. tip::
  ACSL (or ANSI ISO/C Specification Language) is a language made for behavioral specification of C programs.
  See `ACSL description <https://frama-c.com/acsl.html>`_ for more information


Frama-C integration in Sentry
"""""""""""""""""""""""""""""

Sentry kernel build system is based on the ``meson`` build system, and in order to make proof execution
easy and reproducible, Frama-C analysis have been added as ``test()`` definitions.

It is to note that two main Frama-C plugins are used in Sentry:

   * EVA plugin, in association with rte, in order to demonstrate the absence of RTE in the kernel
   * WP plugin, in order to demonstrate correctness of the Sentry components

Frama-C proofs tests are stored in the ``kernel/proof`` sub-directory, separated in different, complementary, analysis.

While EVA analysis are made by defining analysis entrypoint for all effective kernel entrypoints, WP analysis
is made on smaller sub-components, in order to demonstrate separately each of them.

Sentry kernel has the following entrypoints:

   * Kernel bootup entrypoint, that starts with the Reset Handler, which directly calls the effective kernel
     entrypoint, responsible for overall kernel contexts and managers initialization
   * Run time handlers, being:

      * Supervisor calls (syscall) root handler
      * Systick handler (periodically executed)
      * Fault handlers (in case of user or kernel-space faults)

In order to analyze all these entrypoints, the corresponding execution path is analyzed in a separated, dedicated test.
By now the following tests exist:

   * frama-c-parsing: validate that no annotation error exists. Executed as first test
   * frama-c-eva-entrypoint: Execute value analysis of the kernel entrypoint, using the effective ``_entrypoint`` kernel
     startup function directly
   * frama-c-eva-handler-systick: Execute value analyis on the Systick handler, using directly the effective handler implementation as entrypoint
   * frama-c-handler-svc: Executed value analyis on the SVC (syscall) handler, using directly the SVC handler as entrypoint

The coverage calculation is made at analysis time to demonstrate a proper coverage of all callable programs starting with
the given entrypoint.

.. note::
  As there are multiple entrypoints, there are multiple call-graphs associated to it. The coverage being calculated using the
  root program possible paths to demonstrate a complete coverage

.. note::
  Once coverage reaches 100% for all kernel potential entrypoint, all executable kernel code is reached and the analysis is then complete with
  no missing part, excluding only the assembly code, which is not analyzed by Frama-C

To this noRTE analysis, a set of WP tests are added, in order to demonstrate the correctness of the kernel components.
These tests are made on smaller components, starting with the kernel zlib, which is the kernel utility library.
The goal is to demonstrate that the overall kernel components are correct, meaning that they do what they are required to do,
and not only being exempted of RTE.

When launching Frama-C analysis, a directory is forged for each test in the build directory.
Once executed, the corresponding Frama-C analysis is hold and accessible through multiple generated files:

   * ``testname-all.log``: full log file of the analysis, including kernel, user, and all plugin logs
   * ``testname-user.log``: log file of all user-related logs
   * ``testname-md.log``: log file of the md (markdown) plugin
   * ``testname.session.error``: if the test fails, the session file that hold the critical errors for analysis. To be used with ``frama-c-gui`` or ``ivette`` graphical tool
   * ``testname-coverage.json``: entrypoint coverage in JSON format
   * ``testname.red``: Any *Red Alarm* found (RTE that has been demonstrated as effective), to be fixed at first
   * ``testname-report.md``: Analysis report, in markdown format for pdf or website generation
   * ``testname.flamegraph``: Flamegraph of the analysis, that shows relative analysis cost (in time) of each element
   * ``testname.session``: Global session file that hold analyzed source code, :ref:`AST <ast_def>` and all alarms, values and useful elements of the analysis. To be used with ``frama-c-gui`` or ``ivette`` for post-processing

.. _ast_def:

.. tip::
  AST, or Abstract Syntax Tree, is an internal representation of a program structure when any language specific sugars and abstractions are removed

Impact of formal proofness in kernel design
"""""""""""""""""""""""""""""""""""""""""""

In order to ensure efficient and easier analysis from the Frama-C framework, a set of requirements is defined on
the way to specify, implement and separate various kernel sub-components:

   * All kernel sub-components (meaning drivers, managers, syscalls, handlers, utility library....) must have a
     unified, hardware-independent, API
   * All assembly code must be as reduced as possible and called through small, easy to analyze subprograms, such as static inline functions.
     This allows definition of Frama-C compliant stubs, while keeping easy analysis of ASM code.
   * The Sentry kernel must allow a high level of modularity, making separated module analysis possible, while other modules interface
     behavior is based on public API specification only
   * All memory cell must be, except for very specific cases, strictly typed. This means that there is no union at API level. Moreover,
     all variable must have a strictly typed semantic (e.g. a returned status code... must not be semantically something else than a
     status code)
   * There must not have infinite loops (for e.g. waiting for an external event), as such loops can't be traversed by EVA. Such loop must
     be implemented with timeout mechanism.

Once these requirements fulfill, it is highly easier to validate memory manipulation, detect Run-Time Errors and reduce
false positives.


In order to simplify the usage of Frama-C in the Sentry kernel, a dedicated library is provided, denoted `libproof`.
This library provides a set of macros and functions that simplify the writing of EVA entrypoints, ACSL annotations and so on.
This library is available in the ``kernel/proof/libproof`` directory, and is automatically included in all Frama-C tests.

Frama-C testing is separated in three main parts:

   * entrypoint coverage, set in the `kernel/proof/proof_entrypoint` directory, that ensures that kernel entrypoint is covered and analysed
   * handlers coverage, set in the `kernel/proof/proof_handlers` directory, that ensures that all kernel handlers (ticker, syscalls...)
     are covered and analysed
   * composition tests, in order to ensure correcness of various components separatedly, hosted in the `kernel/proof/proof_composition` directory.
