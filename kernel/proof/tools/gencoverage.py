import re
import argparse
import sys
import os
import xml.etree.ElementTree as ET
from xml.dom import minidom

# ----------------------------- Parsing [metrics:eva:reached-stmts] -----------------------------
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

                # Conserver la meilleure couverture
                if data["percentage"] > existing["percentage"]:
                    aggregated[func] = {
                        "covered": max(existing["covered"], data["covered"]),
                        "total": max(existing["total"], data["total"]),
                        "percentage": data["percentage"]
                    }

    return aggregated

# ----------------------------- Parsing [metrics] -----------------------------
def parse_metrics_block(filepath, source_root):
    """
    Parse le bloc [metrics] et retourne toutes les fonctions connues :
    {
        "function_name": {
            "file": relative_path,
            "total": sloc
        }
    }
    """

    results = {}
    in_metrics = False

    stats_header_pattern = re.compile(
        r"Stats for function <(.+)/([^/]+)>"
    )
    sloc_pattern = re.compile(r"Sloc\s*=\s*(\d+)")

    current_function = None
    current_file = None

    with open(filepath, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()

            if line == "[metrics]":
                in_metrics = True
                continue

            if in_metrics and line.startswith("[") and line.endswith("]"):
                break

            if not in_metrics:
                continue

            header_match = stats_header_pattern.search(line)
            if header_match:
                abs_path = header_match.group(1)
                func_name = header_match.group(2)

                full_path = abs_path.rstrip("/")
                rel_path = os.path.relpath(full_path, source_root)

                current_function = func_name
                current_file = rel_path
                continue

            if current_function:
                sloc_match = sloc_pattern.search(line)
                if sloc_match:
                    sloc = int(sloc_match.group(1))

                    results[current_function] = {
                        "file": current_file,
                        "total": sloc
                    }

                    current_function = None
                    current_file = None

    return results

# ----------------------------- Construction dictionnaire global -----------------------------
def build_full_coverage_dict(metrics_files, source_root):
    """
    Construit le dictionnaire complet basé sur :
    - bloc [metrics] → toutes les fonctions
    - bloc [metrics:eva:reached-stmts] → fonctions couvertes
    """

    all_functions = {}
    covered_functions = aggregate_metrics(metrics_files)

    # 1️⃣ Extraire toutes les fonctions depuis bloc [metrics]
    for filepath in metrics_files:
        metrics_block = parse_metrics_block(filepath, source_root)

        for func, data in metrics_block.items():
            all_functions[func] = data

    # 2️⃣ Construire dictionnaire final
    final_dict = {}

    for func, info in all_functions.items():
        total = info["total"]
        file_path = info["file"]

        if func in covered_functions:
            covered = covered_functions[func]["covered"]
        else:
            covered = 0

        final_dict[func] = {
            "file": file_path,
            "total": total,
            "covered": covered,
            "percentage": (covered / total * 100) if total else 0.0
        }

    return final_dict

# ----------------------------- XML SonarQube -----------------------------
def generate_sonarqube_coverage(metrics_dict, output_file):
    """
    Génère un XML compatible SonarQube Generic Coverage.
    """
    coverage = ET.Element("coverage", version="1")

    # Grouper par fichier
    files_map = {}
    for func_data in metrics_dict.values():
        path = func_data["file"]
        files_map.setdefault(path, []).append(func_data)

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
                    covered="true" if line_number <= covered else "false"
                )

    rough_string = ET.tostring(coverage, encoding="utf-8")
    reparsed = minidom.parseString(rough_string)
    pretty_xml = reparsed.toprettyxml(indent="  ")

    with open(output_file, "w", encoding="utf-8") as f:
        f.write(pretty_xml)

# ----------------------------- Résumé global -----------------------------
def print_real_summary(full_dict):
    total_lines = 0
    total_covered = 0
    files = set()

    for data in full_dict.values():
        total_lines += data["total"]
        total_covered += data["covered"]
        files.add(data["file"])

    coverage = (total_covered / total_lines * 100) if total_lines else 0.0

    print("\n===== GLOBAL COVERAGE (metrics-based) =====")
    print(f"Files analysed      : {len(files)}")
    print(f"Total functions     : {len(full_dict)}")
    print(f"Lines covered       : {total_covered}")
    print(f"Total lines (SLOC)  : {total_lines}")
    print(f"Overall coverage    : {coverage:.2f} %")
    print("===========================================\n")

# ----------------------------- Main -----------------------------
def main():
    parser = argparse.ArgumentParser(
        description="Agrégation de rapports coverage + mapping sources"
    )

    parser.add_argument(
        "--files",
        nargs="+",
        required=True,
        help="Liste des fichiers testlog à parser"
    )

    parser.add_argument(
        "--source-path",
        required=True,
        help="Répertoire racine des sources C"
    )

    parser.add_argument(
        "--sonar-output",
        required=True,
        help="Fichier XML SonarQube en sortie"
    )

    args = parser.parse_args()

    full_dict = build_full_coverage_dict(args.files, args.source_path)

    generate_sonarqube_coverage(full_dict, args.sonar_output)

    print(f"Rapport SonarQube généré : {args.sonar_output}")

    print_real_summary(full_dict)

# ----------------------------- Entrée -----------------------------
if __name__ == "__main__":
    main()
