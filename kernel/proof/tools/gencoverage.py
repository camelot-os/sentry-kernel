#!/usr/bin/env python3

import re
import argparse
import sys
import os
import xml.etree.ElementTree as ET
from xml.dom import minidom


def parse_single_file(filepath):
    """
    Parse un seul fichier testlog et retourne un dictionnaire intermédiaire.
    """
    results = {}
    in_block = False

    line_pattern = re.compile(
        r'^([^:]+):\s+(\d+)\s+stmts\s+out\s+of\s+(\d+)\s+\(([\d\.]+)%\)'
    )
    suffix_pattern = re.compile(r'_(\d+)$')

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

                    results[clean_name] = {
                        "covered": covered,
                        "total": total,
                        "percentage": percentage
                    }

    return results


def aggregate_metrics(file_list):
    """
    Agrège plusieurs fichiers testlog en un seul dictionnaire.
    Règle : on conserve la meilleure couverture observée.
    """
    aggregated = {}

    for filepath in file_list:
        try:
            file_metrics = parse_single_file(filepath)
        except FileNotFoundError:
            print(f"Fichier introuvable : {filepath}")
            continue

        for func, data in file_metrics.items():

            if func not in aggregated:
                aggregated[func] = data
            else:
                existing = aggregated[func]

                # On conserve la meilleure couverture
                if data["percentage"] > existing["percentage"]:
                    aggregated[func] = {
                        "covered": max(existing["covered"], data["covered"]),
                        "total": max(existing["total"], data["total"]),
                        "percentage": data["percentage"]
                    }

    return aggregated

def generate_coverage_xml(metrics_dict, output_file):
    """
    Génère un XML conforme au schéma fourni.
    """

    coverage = ET.Element("coverage", version="1")

    # Grouper par fichier
    files_map = {}
    for func, data in metrics_dict.items():
        path = data["file"]
        files_map.setdefault(path, []).append(data)

    for path, functions in files_map.items():
        file_elem = ET.SubElement(coverage, "file", path=path)

        for data in functions:
            total = data["total"]
            covered = data["covered"]

            for line_number in range(1, total + 1):
                ET.SubElement(
                    file_elem,
                    "lineToCover",
                    lineNumber=str(line_number),
                    covered=str(line_number <= covered).lower()
                )

    # Pretty print
    rough_string = ET.tostring(coverage, encoding="utf-8")
    reparsed = minidom.parseString(rough_string)
    pretty_xml = reparsed.toprettyxml(indent="  ")

    with open(output_file, "w", encoding="utf-8") as f:
        f.write(pretty_xml)


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
                    rel_path = os.path.relpath(full_path, os.curdir)
                    found[sym] = rel_path

    return found


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
        required=True,
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
            data["file"] = implementations[sym]
            final_dict[sym] = data

    # Affichage final
    generate_coverage_xml(final_dict, args.xml_output)
    print(f"XML généré dans {args.xml_output}")


if __name__ == "__main__":
    main()

