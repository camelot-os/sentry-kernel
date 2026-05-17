// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#define xstr(s) str(s)
#define str(s) #s
#include <sentry/job.h>

{
    "$schema": "http://json-schema.org/draft-07/schema#",
    "title": "Schema for task metadata",
    "type": "object",
    "properties": {
      "magic": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["uint64_t"]
          },
          "rust_type": {
            "enum":["u64"]
          },
          "value": {
            "type": "number"
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "version": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["uint32_t"]
          },
          "rust_type": {
            "enum":["u32"]
          },
          "value": {
            "type": "number"
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "label": {
        "type": "object",
        "properties": {
          "c_type": {
            "type": "uint32_t"
          },
          "rust_type": {
            "type": "u32"
          },
          "value": {
            "type": "number",
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "priority": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["uint8_t"]
          },
          "rust_type": {
            "enum":["u8"]
          },
          "value": {
            "type": "number"
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "quantum": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["uint8_t"]
          },
          "rust_type": {
            "enum":["u8"]
          },
          "value": {
            "type": "number"
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "capabilities": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["uint32_t"]
          },
          "rust_type": {
            "enum":["u32"]
          },
          "value": {
            "type": "number"
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "flags": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["job_flags_t"]
          },
          "rust_type": {
            "enum":["JobFlags"]
          },
          "value": {
            "type": "object",
            "properties": {
              "start_mode": {
                "enum":[
                  xstr(JOB_FLAG_START_NOAUTO),
                  xstr(JOB_FLAG_START_AUTO)
                ]
              },
              "exit_mode": {
                "enum":[
                  xstr(JOB_FLAG_EXIT_NORESTART),
                  xstr(JOB_FLAG_EXIT_RESTART),
                  xstr(JOB_FLAG_EXIT_PANIC),
                  xstr(JOB_FLAG_EXIT_PERIODICRESTART)
                ]
              }
            },
            "required": [
              "start_mode",
              "exit_mode"
            ]
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "s_text": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["size_t"]
          },
          "rust_type": {
            "enum":["usize"]
          },
          "value": {
            "type": "number"
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "text_size": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["size_t"]
          },
          "rust_type": {
            "enum":["usize"]
          },
          "value": {
            "type": "number"
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "s_got": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["size_t"]
          },
          "rust_type": {
            "enum":["usize"]
          },
          "value": {
            "type": "number"
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "got_size": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["size_t"]
          },
          "rust_type": {
            "enum":["usize"]
          },
          "value": {
            "type": "number"
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "rodata_size": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["size_t"]
          },
          "rust_type": {
            "enum":["usize"]
          },
          "value": {
            "type": "number"
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "data_size": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["size_t"]
          },
          "rust_type": {
            "enum":["usize"]
          },
          "value": {
            "type": "number"
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "bss_size": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["size_t"]
          },
          "rust_type": {
            "enum":["usize"]
          },
          "value": {
            "type": "number"
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "heap_size": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["size_t"]
          },
          "rust_type": {
            "enum":["usize"]
          },
          "value": {
            "type": "number"
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "s_svcexchange": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["size_t"]
          },
          "rust_type": {
            "enum":["usize"]
          },
          "value": {
            "type": "number"
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "stack_size": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["uint16_t"]
          },
          "rust_type": {
            "enum":["u16"]
          },
          "value": {
            "type": "number"
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "entrypoint_offset": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["uint16_t"]
          },
          "rust_type": {
            "enum":["u16"]
          },
          "value": {
            "type": "number"
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "finalize_offset": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["uint16_t"]
          },
          "rust_type": {
            "enum":["u16"]
          },
          "value": {
            "type": "number"
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "num_shm": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["uint8_t"]
          },
          "rust_type": {
            "enum":["u8"]
          },
          "value": {
            "type": "number",
            "minimum": 0,
            "maximum": CONFIG_MAX_SHM_PER_TASK
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "shms": {
        "type": "array",
        "items": {
          "type": "object",
          "properties": {
            "c_type": {
                "enum":["shmh_t"]
            },
            "rust_type": {
                "enum":["SHMHandle"]
            },
            "value": {
              "type": "number",
            },
            "description": {
              "type": "string"
            }
          },
          "required": [
            "c_type",
            "rust_type",
            "value",
            "description"
          ]
        },
        "minItems": 0,
        "maxItems": CONFIG_MAX_SHM_PER_TASK
      },
      "num_dev": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["uint8_t"]
          },
          "rust_type": {
            "enum":["u8"]
          },
          "value": {
            "type": "number",
            "minimum": 0,
            "maximum": CONFIG_MAX_DEV_PER_TASK
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "devs": {
        "type": "array",
        "items": {
          "type": "number",
          "properties": {
            "c_type": {
                "enum":["devh_t"]
            },
            "rust_type": {
                "enum":["DEVHandle"]
              },
            "value": {
              "type": "number",
            },
            "description": {
              "type": "string"
            }
          },
          "required": [
            "c_type",
            "rust_type",
            "value",
            "description"
          ]
        },
        "minItems": 0,
        "maxItems": CONFIG_MAX_DEV_PER_TASK
      },
      "num_dma": {
        "type": "object",
        "properties": {
          "c_type": {
            "enum":["uint8_t"]
          },
          "rust_type": {
            "enum":["u8"]
          },
          "value": {
            "type": "number",
            "minimum": 0,
            "maximum": CONFIG_MAX_DMA_STREAMS_PER_TASK
          },
          "description": {
            "type": "string"
          }
        },
        "required": [
          "c_type",
          "rust_type",
          "value",
          "description"
        ]
      },
      "dmas": {
        "type": "array",
        "items": {
          "type": "object",
          "properties": {
            "c_type": {
                "enum":["dmah_t"]
              },
            "rust_type": {
                "enum":["DMAHandle"]
              },
            "value": {
              "type": "number",
            },
            "description": {
              "type": "string"
            }
          },
          "required": [
            "c_type",
            "rust_type",
            "value",
            "description"
          ]
        },
        "minItems": 0,
        "maxItems": CONFIG_MAX_DMA_STREAMS_PER_TASK
      },
      "task_sha256": {
        "type": "array",
        "items": {
          "type": "object",
          "properties": {
            "c_type": {
              "enum":["uint8_t"]
            },
            "rust_type": {
              "enum":["u8"]
            },
            "value": {
              "type": "number"
            }
          },
          "required": [
            "c_type",
            "rust_type",
            "value"
          ]
        }
      },
      "metadata_sha256": {
        "type": "array",
        "items": {
          "type": "object",
          "properties": {
            "c_type": {
                "enum":["uint8_t"]
            },
            "rust_type": {
              "enum":["u8"]
            },
            "value": {
              "type": "number"
            }
          },
          "required": [
            "c_type",
            "rust_type",
            "value"
          ]
        }
      }
    },
    "required": [
      "magic",
      "version",
      "handle",
      "priority",
      "quantum",
      "capabilities",
      "flags",
      "s_text",
      "text_size",
      "rodata_size",
      "data_size",
      "bss_size",
      "heap_size",
      "s_svcexchange",
      "stack_size",
      "entrypoint_offset",
      "finalize_offset",
      "num_shm",
      "shms",
      "num_dev",
      "devs",
      "num_dma",
      "dmas",
      "task_sha256",
      "metadata_sha256"
    ]
  }
