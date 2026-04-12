# SPDX-FileCopyrightText: 2026 H2Lab OSS Team
# SPDX-License-Identifier: Apache-2.0

*** Settings ***

Documentation   Sentry syscall fuzzing report generation
...             Parse autotest output from serial line and produce a RobotFramework report
...             this testsuite requires two variables, being set through resource file or
...             through robot command line (see robotframework manual for that).
...             These variables are:
...             - PROBE_UID: (string) unique id that defines the probe UID (serial identifier)
...               as seen by both pyocd and udev
...             - FIRMWARE_FILE: (string) path to the firmware file (hex or elf) to flash
...               into the target

Library         SerialLibrary
Library         String
Library         Collections
Library         DependencyLibrary
Library         PyocdLibrary    ${PROBE_UID}

*** Variables ***

${PROMPT}                    [FUZZ]
${RISK_TAG}                  [FUZZ][RISK]
${WARN_TAG}                  [FUZZ][WARN]
${SUMMARY_TAG}               [FUZZ][SUMMARY]
${INVALID_SUMMARY_PREFIX}    [FUZZ][SUMMARY] invalid_syscall
${IPC_SUMMARY_PREFIX}        [FUZZ][SUMMARY] ipc_len

*** Test Cases ***

Load Autotest
    [Documentation]         Read autotest content from serial line

    Should Not Be Empty     ${FIRMWARE_FILE}
    Reset
    Load Firmware           ${FIRMWARE_FILE}
    ${vcp}                  Get Probe Vcp
    Log                     Virtual port is ${vcp}
    Open Serial Port        ${vcp}
    Read All
    Resume

    ${read_all}             Read Until  terminator=AUTOTEST END
    Close Serial Port
    Set Suite Variable      ${ALL_LOG}  ${read_all}
    Should Not Be Empty     ${ALL_LOG}
    Log                     ${ALL_LOG}

Extract Fuzz Lines
    [Documentation]         Extract useful fuzzing lines from serial log

    Depends on test         Load Autotest

    ${fuzz_lines}           Get Lines Containing String     ${ALL_LOG}    ${PROMPT}
    Set Suite Variable      ${FUZZ_LOG}    ${fuzz_lines}
    Should Not Be Empty     ${FUZZ_LOG}

Invalid Syscall Stability
    [Documentation]         Validate invalid syscall summary stability

    Depends on test         Extract Fuzz Lines

    ${line}                 Get Lines Containing String     ${FUZZ_LOG}    ${INVALID_SUMMARY_PREFIX}
    Should Not Be Empty     ${line}
    Should Match Regexp     ${line}    (?s).*id=255\s+iters=\d+\s+status=\w+.*

IPC Summary Extraction
    [Documentation]         Extract and validate global IPC campaign summary

    Depends on test         Extract Fuzz Lines

    ${line}                 Get Lines Containing String     ${FUZZ_LOG}    ${IPC_SUMMARY_PREFIX}
    Should Not Be Empty     ${line}

    ${attempts_m}           Get Regexp Matches    ${line}    attempts=(\d+)    1
    ${ok_m}                 Get Regexp Matches    ${line}    ok=(\d+)          1
    ${invalid_m}            Get Regexp Matches    ${line}    invalid=(\d+)     1
    ${trunc_m}              Get Regexp Matches    ${line}    trunc_hits=(\d+)  1
    ${wait_m}               Get Regexp Matches    ${line}    wait_errors=(\d+) 1

    ${attempts}             Set Variable    ${attempts_m}[0]
    ${ok}                   Set Variable    ${ok_m}[0]
    ${invalid}              Set Variable    ${invalid_m}[0]
    ${trunc_hits}           Set Variable    ${trunc_m}[0]
    ${wait_errors}          Set Variable    ${wait_m}[0]

    Should Match Regexp     ${attempts}     ^\d+$
    Should Match Regexp     ${ok}           ^\d+$
    Should Match Regexp     ${invalid}      ^\d+$
    Should Match Regexp     ${trunc_hits}   ^\d+$
    Should Match Regexp     ${wait_errors}  ^\d+$

    Set Suite Variable      ${FUZZ_ATTEMPTS}       ${attempts}
    Set Suite Variable      ${FUZZ_OK}             ${ok}
    Set Suite Variable      ${FUZZ_INVALID}        ${invalid}
    Set Suite Variable      ${FUZZ_TRUNC_HITS}     ${trunc_hits}
    Set Suite Variable      ${FUZZ_WAIT_ERRORS}    ${wait_errors}

Risk And Warning Counters
    [Documentation]         Count RISK and WARN events

    Depends on test         Extract Fuzz Lines

    ${risk_lines}           Get Lines Containing String     ${FUZZ_LOG}    ${RISK_TAG}
    ${warn_lines}           Get Lines Containing String     ${FUZZ_LOG}    ${WARN_TAG}
    ${risk_count}           Get Line Count    ${risk_lines}
    ${warn_count}           Get Line Count    ${warn_lines}

    Set Suite Variable      ${FUZZ_RISK_COUNT}    ${risk_count}
    Set Suite Variable      ${FUZZ_WARN_COUNT}    ${warn_count}

    Should Match Regexp     ${FUZZ_RISK_COUNT}    ^\d+$
    Should Match Regexp     ${FUZZ_WARN_COUNT}    ^\d+$

Truncation Evidence
    [Documentation]         Verify at least one truncation evidence line exists

    Depends on test         Extract Fuzz Lines

    ${ipc_trunc}            Get Lines Containing String     ${FUZZ_LOG}    IPC_TRUNCATION
    Should Not Be Empty     ${ipc_trunc}
    Should Match Regexp     ${ipc_trunc}    (?s).*len_in=\d+\s+len_seen=\d+.*

Fuzz Campaign Totals
    [Documentation]         Produce final campaign summary in Robot report

    Depends on test         IPC Summary Extraction
    Depends on test         Risk And Warning Counters

    Set Test Message    attempts=${FUZZ_ATTEMPTS}, ok=${FUZZ_OK}, invalid=${FUZZ_INVALID}, trunc_hits=${FUZZ_TRUNC_HITS}, wait_errors=${FUZZ_WAIT_ERRORS}, risk_events=${FUZZ_RISK_COUNT}, warn_events=${FUZZ_WARN_COUNT}

*** Keywords ***

Open Serial Port
    [Arguments]     ${serial}
    Connect         ${serial}    115200
    Set Timeout     20

Close Serial Port
    Disconnect
