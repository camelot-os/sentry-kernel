// SPDX-FileCopyrightText: 2024 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */

#include <string>
#include <iostream>
#include <sstream>
#include <array>
#include <stdexcept>

#include <nlohmann/json.hpp>
#include <argparse/argparse.hpp>
#include <openssl/sha.h>

#include "task_meta.hpp"
#include "reflect.hpp"
#include "arch/arch.hpp"

using json = nlohmann::json;

int main(int argc, char *argv[])
{
    argparse::ArgumentParser program("genmetadata", "0", argparse::default_arguments::help);

    program.add_argument("-o", "--output").help("generated metadata blob");
    program.add_argument("json_str").help("input json stream");

    try {
        program.parse_args(argc, argv);
        std::istringstream in{program.get<std::string>("json_str")};
        std::string out{program.get<std::string>("output")};
        auto data = json::parse(in);
        auto meta = taskMetadata::from_json(data["task_meta"]);

        std::array<uint8_t, SHA256_DIGEST_LENGTH> metadata_sha256{};
        if (!meta.set_u8_array_field("metadata_sha256", metadata_sha256)) {
            throw std::runtime_error("metadata_sha256 field not found or has unexpected type");
        }

        auto blob = reflect_to_bytes<arch::memory_spec>(meta);
        if (SHA256(blob.data(), blob.size(), metadata_sha256.data()) == nullptr) {
            throw std::runtime_error("failed to compute metadata_sha256");
        }

        if (!meta.set_u8_array_field("metadata_sha256", metadata_sha256)) {
            throw std::runtime_error("failed to write metadata_sha256 field");
        }

        reflect_to_bin<arch::memory_spec>(meta, out);
    }
    catch (const std::exception& err) {
        std::cerr << err.what() << std::endl;
        std::cerr << program;
        std::exit(1);
    }

    return 0;
}
