<!--
SPDX-FileCopyrightText: 2023-2024 Ledger SAS
SPDX-License-Identifier: Apache-2.0
-->
# Security Policy

## Reporting process

Any Github authenticated user is allowed to to publish private vulnerability
through the [Github security vulnerability process](https://docs.github.com/en/code-security/security-advisories/guidance-on-reporting-and-writing-information-about-vulnerabilities/privately-reporting-a-security-vulnerability)

The locally published security report is kept private as long as:

   * the vulnerability has been assessed
   * the security fix is not written and reviewed
   * a new release has not been delivered including the security fix

The [security embargo](https://googleprojectzero.blogspot.com/p/vulnerability-disclosure-faq.html) is 90 days so that project maintainers can fix, test and deliver fixes.

The report author is free to reserve an associated CVE entry as soon as the embargo is respected.

For any questions and to inform the maintainers of the vulnerability existence, please contact [camelot-os](mailto:camelot-os@h2lab.org) team.

## Supported versions

By now, as the v1.0.0 version is not delivered, security fixes must match a
vulnerability still present on `main` head.

As soon as the first Sentry >=1.0.0 release is delivered, vulnerabilities can also target
the LTS defined releases (if they exist) and last stable releases.
