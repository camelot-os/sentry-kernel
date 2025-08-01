# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

*** Settings ***

Documentation   Sentry Autotest report generation
...             Parse autotest output on serial port and analyse its content
...             this testsuite requires two variables, being set through ressource file or though
...             robot command line (see robotframework manual for that).
...             These variable are:
...             - PROBE_UID: (string) unique id that defines the probe UID (serial identifier) as seen by both pyocd and udev
...             - FIRMWARE_FILE: (string) path to the firmware file (hex or elf) to flash into the target

Library         SerialLibrary
Library         String
Library         DependencyLibrary
Library         PyocdLibrary    ${PROBE_UID}

*** Variables ***

${PROMPT}          [AT]
${SOCLINE}             _entrypoint: booting on SoC

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
    Log                     ${ALL_LOG}

Extract Logs
    ${read_AT}              Get Lines Containing String     ${ALL_LOG}	[AT]
    Set Suite Variable      ${AT_LOG}  ${read_AT}
    Should Contain          ${read_AT}    ${PROMPT}
    Log                     ${AT_LOG}

Target Metadata
    ${SoC_Line}             Get Lines Containing String     ${ALL_LOG}      _entrypoint: booting on SoC
    ${SoC}                  Fetch From Right    ${SoC_Line}     ${SPACE}
    ${Dts_Line}             Get Lines Containing String     ${ALL_LOG}      _entrypoint: configured dts file
    ${Dts}                  Fetch From Right    ${Dts_Line}     ${SPACE}
    Set Test Message        firmware: boot on  SoC ${SoC} with DTS: ${Dts}


AT Yield
    [Documentation]         Parse yield API autotest results

    Depends on test         Load Autotest
    ${suite}                Get Lines Containing String	${AT_LOG}	test_yield
    Log                     ${suite}
    Should Not Be Empty     ${suite}
    Should Not Contain      ${suite}   KO
    Suite Result            ${suite}

AT Get Handle
    [Documentation]         Parse handle API autotest results

    Depends on test         Load Autotest
    ${suite}                Get Lines Containing String	${AT_LOG}	test_gethandle
    Log                     ${suite}
    Should Not Be Empty     ${suite}
    Should Not Contain      ${suite}   KO
    Suite Result            ${suite}

AT Signals
    [Documentation]         Parse signals API autotest results

    Depends on test         Load Autotest
    ${suite}                Get Lines Containing String	${AT_LOG}	test_signal
    Log                     ${suite}
    Should Not Be Empty     ${suite}
    Should Not Contain      ${suite}   KO
    Suite Result            ${suite}

AT IPCs
    [Documentation]         Parse IPC API autotest results

    Depends on test         Load Autotest
    ${suite}                Get Lines Containing String	${AT_LOG}	test_ipc
    Log                     ${suite}
    Should Not Be Empty     ${suite}
    Should Not Contain      ${suite}   KO
    Suite Result            {suite}

AT KRNG
    [Documentation]         Parse KRNG API autotest results

    Depends on test         Load Autotest
    ${suite}                Get Lines Containing String	${AT_LOG}	test_random
    Log                     ${suite}
    Should Not Be Empty     ${suite}
    Should Not Contain      ${suite}   KO
    Suite Result            ${suite}

AT Sleep
    [Documentation]         Parse sleep API autotest results

    Depends on test         Load Autotest
    ${suite}                Get Lines Containing String	${AT_LOG}	test_sleep
    Log                     ${suite}
    Should Not Be Empty     ${suite}
    Should Not Contain      ${suite}   KO
    Suite Result            ${suite}

AT GPIOs
    [Documentation]         Parse GPIO API autotest results

    Depends on test         Load Autotest
    ${suite}                Get Lines Containing String	${AT_LOG}	test_gpio
    Log                     ${suite}
    Should Not Be Empty     ${suite}
    Should Not Contain      ${suite}   KO
    Suite Result            ${suite}

AT Cycles measurment
    [Documentation]         Parse Cycle API autotest results

    Depends on test         Load Autotest
    ${suite}                Get Lines Containing String	${AT_LOG}	test_cycles
    Log                     ${suite}
    Should Not Be Empty     ${suite}
    Should Not Contain      ${suite}   KO
    Suite Result            ${suite}

AT SHM
    [Documentation]         Parse SHM API autotest results

    Depends on test         Load Autotest
    ${suite}                Get Lines Containing String	${AT_LOG}	test_shm
    Log                     ${suite}
    Should Not Be Empty     ${suite}
    Should Not Contain      ${suite}   KO
    Suite Result            ${suite}

AT Map
    [Documentation]         Parse map API autotest results

    Depends on test         Load Autotest
    ${suite}                Get Lines Containing String	${AT_LOG}	test_map
    Log                     ${suite}
    Should Not Contain      ${suite}   KO
    Suite Result            ${suite}

AT DMAs
    [Documentation]     Parse DMA API autotest results

    Depends on test     Load Autotest
    ${suite}            Get Lines Containing String	${AT_LOG}	test_dma
    Log                 ${suite}
    Should Not Contain  ${suite}   KO
    Suite Result        ${suite}

AT IRQ
    [Documentation]     Parse user IRQ API autotest results

    Depends on test     Load Autotest
    ${suite}            Get Lines Containing String	${AT_LOG}	test_irq
    Log                 ${suite}
    Should Not Contain  ${suite}   KO
    Suite Result        ${suite}

AT Capabilities
    [Documentation]     Parse Capabilities autotest results

    Depends on test     Load Autotest
    ${suite}            Get Lines Containing String	${AT_LOG}	test_capa
    Log                 ${suite}
    Should Not Contain  ${suite}   KO
    Suite Result        ${suite}

Autotest Totals
    [Documentation]         Calculate total numbers of Success and KOs

    Depends on test         Load Autotest
    Suite Result            ${AT_LOG}

Fault Detection
    [Documentation]         Check if a fault is triggered

    Depends on test         Load Autotest
    ${handler}              Get Lines Containing String	${ALL_LOG}	fault_handler
    ${frame}                Get Lines Containing String	${ALL_LOG}	dump_frame
    Log                     ${handler}
    Log                     ${frame}
    Should Be Empty         ${handler}
    Should Be Empty         ${frame}

*** Keywords ***

Open Serial Port
    [Arguments]     ${serial}
    Connect         ${serial}    115200
    Set Timeout     20

Close Serial Port
    Disconnect

Suite Result
    [Arguments]         ${suite}

    ${success}          Get Lines Containing String	${suite}	SUCCESS
    ${success_num}      Get Line Count  ${success}
    ${KO}          Get Lines Containing String	${suite}	KO
    ${KO_num}      Get Line Count  ${KO}
    Set Test Message    Success: ${success_num}, KOs: ${KO_num}
