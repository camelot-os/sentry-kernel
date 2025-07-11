<!--
SPDX-FileCopyrightText: 2023-2024 Ledger SAS
SPDX-License-Identifier: Apache-2.0
-->

# Contribution Guidelines

Being an open-source project, we encourage the community to submit patches and issues
directly to the project.
This project is made to be collaborative, and we appreciate the usage of standards and
collaboratibe methods for submissions.

## To begin with:

* Sentry kernel uses the permissive `Apache 2.0 license`, that allows gree use, dmofication
  and redistribution of any project using this kernel.

* The Sentry kernel uses SPDX standard for license declaration. The usage of Reuse is used
  in order to validate that all project peaces properly specify the according license.

* The Developer Certificate of Origin (DCO) process is followed to
  ensure developers are following licensing criteria for their
  contributions, and documented with a ``Signed-off-by`` line in commits.

* Sentry kernel development workflow is supported on Linux, macOS, and Windows.

* Source code for the project is maintained in the GitHub repo:
  https://github.com/camelot-os/sentry-kernel

* Issues, features and security tracking is done with Github issues, pull-requests and security reports.
  Milestones are used in order to define a clearer roadmap.

* A Continuous Integration (CI) system runs on every Pull Request (PR). This includes the formal proofness (noRTE) analysis.

* A Discord channel denoted CamelotOS is dedicated to exchanges with the community. This repository also has the Github
  discussions interface active for any questions or requests.

## Contribution buidelines

The following guidelines must be respected by all contributors:

* When contributing, please use the ususal fork+pull-request Github model.

* When publishing a bug through issues, please specify properly the use case and a way de reproduce.

* When proposing a feature, be sure to properly define the usage, and ensure that the according documentation in the `doc/concepts` is properly made.
  If the feature includes a new or updated syscall, consider adding its full description respecting the usual man format chapters in
  the `docs/concepts/uapi/syscalls` directory, so that corresponding man page will be generated.

* By now, as the kernel implementation is in early stage, PRs should target the `main` branch.

* If a contribution requires a large amount of code, please decompose in multiple consecutive pull-requests, to make PR review easier.

* All pull-request will be checked for non-regression using the kernel *autotest* build profile, that include a dedicated Autotest application stored in
  this very repository. No regression is allowed.

* All modified file must have the SPDX header copyright line updated with the PR author. All new file must have a proper SPDX header (checked by CI).

* Please avoid adding new external dependencies. Dependabot is used for dependency analysis but their number should stay small enough.

* When publising a vulnerability fix, the PR title **must** start with `cve:` tag and be dedicated to CVE fix.
