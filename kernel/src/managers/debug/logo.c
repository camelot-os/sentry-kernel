// SPDX-FileCopyrightText: 2025 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0

#include <sentry/managers/debug.h>


#if defined(CONFIG_DEBUG_LOGO)
#if defined(CONFIG_DEBUG_LOGO_COLORED)
/* ASCII standard echapment codes for foreground characters */
#define COLOR_FG_BLUE   "\e[0;34m"
#define COLOR_FG_RESET  "\e[0m"
#else
#define COLOR_FG_BLUE
#define COLOR_FG_RESET
#endif

static const char * const h2lab[] = {
"                    ......." COLOR_FG_BLUE "####" COLOR_FG_RESET "..\n",
"              ......." COLOR_FG_BLUE "*########" COLOR_FG_RESET "........\n",
"          ....." COLOR_FG_BLUE "*##############" COLOR_FG_RESET "....=" COLOR_FG_BLUE "#######" COLOR_FG_RESET "..\n",
"          ..." COLOR_FG_BLUE "#######" COLOR_FG_RESET "....." COLOR_FG_BLUE "*##@##########*" COLOR_FG_RESET ".....\n",
"             ..........." COLOR_FG_BLUE "+##########" COLOR_FG_RESET "........\n",
"       ...       ...." COLOR_FG_BLUE "##########" COLOR_FG_RESET "........\n",
"      .." COLOR_FG_BLUE "###" COLOR_FG_RESET "...       .............       +++++++\n",
"     ..." COLOR_FG_BLUE "####" COLOR_FG_RESET "......                   +++++++++++\n",
"      .." COLOR_FG_BLUE "####" COLOR_FG_RESET "....." COLOR_FG_BLUE "##" COLOR_FG_RESET "..            +++++++++++++++\n",
"      .." COLOR_FG_BLUE "####" COLOR_FG_RESET "....:" COLOR_FG_BLUE "####" COLOR_FG_RESET ".         ++++++++++++ ++++\n",
"      ..." COLOR_FG_BLUE "###" COLOR_FG_RESET "-...." COLOR_FG_BLUE "####" COLOR_FG_RESET "..       ++++++++++++++++++\n",
"      ..." COLOR_FG_BLUE "####" COLOR_FG_RESET "...:" COLOR_FG_BLUE "####" COLOR_FG_RESET "...     +++++++++++++ +++++\n",
"      ..." COLOR_FG_BLUE "#######" COLOR_FG_RESET "." COLOR_FG_BLUE "####" COLOR_FG_RESET "....    ++++ ++++  ++ ++ ++\n",
"      ..." COLOR_FG_BLUE "############" COLOR_FG_RESET "....   +++++ +++++ ++++++++\n",
"      ..." COLOR_FG_BLUE "############" COLOR_FG_RESET "....   +++++++++++++  +++++\n",
"       .." COLOR_FG_BLUE "####" COLOR_FG_RESET "..." COLOR_FG_BLUE "#####" COLOR_FG_RESET "....   ++++ ++ ++ ++++++++\n",
"        ." COLOR_FG_BLUE "####" COLOR_FG_RESET "...." COLOR_FG_BLUE "####" COLOR_FG_RESET "....   ++++ ++  +++++++++\n",
"         ." COLOR_FG_BLUE "###" COLOR_FG_RESET "...." COLOR_FG_BLUE "####" COLOR_FG_RESET "....   ++++ ++++++++++++\n",
"          ......." COLOR_FG_BLUE "####" COLOR_FG_RESET "....   ++++++++++++++++\n",
"             ...." COLOR_FG_BLUE "####" COLOR_FG_RESET "....   ++++++++++++++\n",
"               ..." COLOR_FG_BLUE "###" COLOR_FG_RESET "....   +++++++++++\n",
"                  ......    ++++++++\n",
"                              ++\n",
NULL,
};

void logo_print(void) {
    // Print the h2lab ASCII art
    size_t i = 0;
    while (h2lab[i] != NULL) {
        printk("%s", h2lab[i++]);
    }
}
#else
void logo_print(void) {
    // Do nothing if not in debug or autotest mode
}
#endif
