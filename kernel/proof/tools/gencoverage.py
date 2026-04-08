#!/usr/bin/env python3

import re
import argparse
import sys
import os
import xml.etree.ElementTree as ET
from xml.dom import minidom

def parse_reached_stmts(filepath):
    results = {}
    in_block = False

    line_pattern = re.compile(
        r'^([^:]+):\s+(\d+)\s+stmts\s+out\s+of\s+(\d+)\s+\(([\d\.]+)%\)'
    )

    suffix_pattern = re.compile(r'_(\d+)$')

    try:
        with open(filepath, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()

                if line == "[metrics:eva:reached-stmts]":
                    in_block = True
                    continue

                if in_block and line.startswith("[") and line.endswith("]"):
                    break

                if in_block:
                    match = line_pattern.match(line)
                    if match:
                        raw_name = match.group(1)
                        covered = int(match.group(2))
                        total = int(match.group(3))
                        percentage = float(match.group(4))

                        clean_name = suffix_pattern.sub("", raw_name)

                        entry = {
                            "covered": covered,
                            "total": total,
                            "percentage": percentage
                        }

                        if clean_name in results:
                            if percentage > results[clean_name]["percentage"]:
                                results[clean_name] = entry
                        else:
                            results[clean_name] = entry

    except FileNotFoundError:
        print(f"Erreur : fichier introuvable -> {filepath}")
        sys.exit(1)

    return results


def find_function_implementations(symbols, source_root):
    """
    Recherche les implémentations des symboles dans les fichiers .c et .h.
    Retourne un mapping {symbol: relative_path}
    """

    symbol_patterns = {
        sym: re.compile(
            rf'\b{re.escape(sym)}\s*\([^;{{]*\)\s*\{{'
        )
        for sym in symbols
    }

    found = {}

    for root, _, files in os.walk(source_root):
        for file in files:
            if not file.endswith((".c", ".h")):
                continue

            full_path = os.path.join(root, file)

            try:
                with open(full_path, "r", encoding="utf-8", errors="ignore") as f:
                    content = f.read()
            except Exception:
                continue

            for sym, pattern in symbol_patterns.items():
                if sym in found:
                    continue

                if pattern.search(content):
                    rel_path = os.path.relpath(full_path, source_root)
                    found[sym] = rel_path

    return found

def print_global_summary(final_dict):
    """
    Affiche un résumé global de la couverture.
    """

    total_covered = 0
    total_lines = 0
    files_set = set()

    for data in final_dict.values():
        total_covered += data["covered"]
        total_lines += data["total"]
        files_set.add(data["file"])

    if total_lines == 0:
        coverage = 0.0
    else:
        coverage = (total_covered / total_lines) * 100

    print("\n===== Coverage Summary =====")
    print(f"Files analysed : {len(files_set)}")
    print(f"Functions      : {len(final_dict)}")
    print(f"Lines covered  : {total_covered}")
    print(f"Lines total    : {total_lines}")
    print(f"Coverage       : {coverage:.2f} %")
    print("============================\n")


def generate_sonar_generic_coverage(file_dict, output_file="sonar_coverage.xml"):
    """
    Génère un rapport SonarQube Generic Coverage XML.

    Format attendu :
    <coverage version="1">
      <file path="...">
        <lineToCover lineNumber="X" covered="true|false"/>
      </file>
    </coverage>
    """

    root = ET.Element("coverage", attrib={"version": "1"})

    for file_path, data in sorted(file_dict.items()):
        total_lines = data.get("total_lines", set())
        covered_lines = data.get("covered_lines", set())

        if not total_lines:
            continue

        file_elem = ET.SubElement(root, "file", attrib={"path": file_path})

        for line_number in sorted(total_lines):
            ET.SubElement(
                file_elem,
                "lineToCover",
                attrib={
                    "lineNumber": str(line_number),
                    "covered": "true" if line_number in covered_lines else "false"
                }
            )

    # Pretty print
    rough_string = ET.tostring(root, encoding="utf-8")
    reparsed = minidom.parseString(rough_string)
    pretty_xml = reparsed.toprettyxml(indent="  ")

    with open(output_file, "w", encoding="utf-8") as f:
        f.write(pretty_xml)

    print(f"SonarQube Generic Coverage généré : {output_file}")


def lines_covered_per_file(coverage_dict, source_root):
    """
    Retourne un dictionnaire :

    {
        "file_path": {
            "covered_lines": set(...),
            "total_lines": set(...)
        }
    }

    total_lines contient uniquement :
      - lignes dans des fonctions
      - non vides
      - non commentaires
    """

    result = {}

    for func_name, data in coverage_dict.items():
        file_path = data["file"]
        covered_count = data["covered"]

        full_path = os.path.abspath(file_path)
        if not os.path.isfile(full_path):
            continue

        with open(full_path, "r", encoding="utf-8", errors="ignore") as f:
            content = f.read()

        # --- Pattern amélioré ---
        pattern = re.compile(
            r'^.*\s+{}\s*\([^;]*?\)\s*(?:\n\s*)*\{{'.format(re.escape(func_name)),
            re.MULTILINE | re.DOTALL
        )

        match = pattern.search(content)
        if not match:
            continue

        start_pos = match.start()
        start_line = content.count("\n", 0, start_pos) + 1

        # --- Trouver fin réelle par équilibrage des accolades ---
        brace_count = 0
        in_function = False
        end_pos = None

        for i in range(match.end() - 1, len(content)):
            char = content[i]

            if char == "{":
                brace_count += 1
                in_function = True
            elif char == "}":
                brace_count -= 1
                if in_function and brace_count == 0:
                    end_pos = i
                    break

        if end_pos is None:
            continue

        end_line = content.count("\n", 0, end_pos) + 1

        # Découpage en lignes
        lines = content.splitlines()

        if file_path not in result:
            result[file_path] = {
                "covered_lines": set(),
                "total_lines": set()
            }

        inside_block_comment = False
        instruction_lines = []

        # --- Analyse ligne par ligne dans la fonction ---
        for line_number in range(start_line, end_line + 1):
            line = lines[line_number - 1].strip()

            # Gestion commentaires multilignes
            if inside_block_comment:
                if "*/" in line:
                    inside_block_comment = False
                continue

            if line.startswith("/*"):
                if "*/" not in line:
                    inside_block_comment = True
                continue

            if line.startswith("//"):
                continue

            if not line:
                continue

            # Ligne considérée comme instruction
            instruction_lines.append(line_number)
            result[file_path]["total_lines"].add(line_number)

        # --- Appliquer couverture sur les N premières lignes instructionnelles ---
        for line_number in instruction_lines[:covered_count]:
            result[file_path]["covered_lines"].add(line_number)

    return result

def main():
    parser = argparse.ArgumentParser(
        description="Extraction coverage + localisation des implémentations C"
    )
    parser.add_argument(
        "--file",
        required=True,
        help="Fichier de métriques"
    )
    parser.add_argument(
        "--source-path",
        required=False,
        default="kernel",
        help="Répertoire racine des sources C"
    )
    parser.add_argument(
        "--xml-output",
        required=True,
        help="Fichier XML de sortie"
    )

    args = parser.parse_args()

    metrics_dict = parse_reached_stmts(args.file)

    implementations = find_function_implementations(
        metrics_dict.keys(),
        args.source_path
    )

    # Suppression des fonctions non trouvées
    final_dict = {}
    for sym, data in metrics_dict.items():
        if sym in implementations:
            data["file"] = "kernel/" + implementations[sym]
            final_dict[sym] = data
    # Keep only sentry kernel files
    filtered_dict = {
        func: data
        for func, data in final_dict.items()
        if "kernel/src" in data["file"] or "kernel/include" in data["file"]
    }
    srcoveraqe_dict = lines_covered_per_file(filtered_dict, args.source_path)


    print(srcoveraqe_dict.items())

    generate_sonar_generic_coverage(srcoveraqe_dict, args.xml_output)
    print(f"XML généré dans {args.xml_output}")
    print_global_summary(filtered_dict)


if __name__ == "__main__":
    main()
