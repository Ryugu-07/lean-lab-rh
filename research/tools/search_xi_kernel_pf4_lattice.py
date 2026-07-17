#!/usr/bin/env python3
"""Enumerate non-Toeplitz 4x4 minors on common rational lattices.

The output selects possible Lean targets only. Every determinant used as proof
evidence must be reconstructed from the complete kernel inside Lean.
"""

from __future__ import annotations

import argparse
from itertools import combinations
import json

import numpy as np

from search_xi_kernel_pf4 import candidate_key, phi, verify_candidate


def matrix_metrics(matrix: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    determinant = np.linalg.det(matrix)
    row_scale = np.prod(np.max(np.abs(matrix), axis=2), axis=1)
    relative = np.full(determinant.shape, np.inf, dtype=np.float64)
    np.divide(determinant, row_scale, out=relative, where=row_scale > 0.0)
    return determinant, relative


def condition_numbers(matrix: np.ndarray) -> np.ndarray:
    singular_values = np.linalg.svd(matrix, compute_uv=False)
    result = np.full(matrix.shape[0], np.inf, dtype=np.float64)
    np.divide(
        singular_values[:, 0],
        singular_values[:, -1],
        out=result,
        where=singular_values[:, -1] > 0.0,
    )
    return result


def retain_record(
    retained: list[dict[str, object]],
    record: dict[str, object],
    retain: int,
) -> None:
    retained.append(record)
    retained.sort(key=candidate_key)
    del retained[retain:]


def run(args: argparse.Namespace) -> dict[str, object]:
    subsets = np.asarray(list(combinations(range(args.grid_size), 4)), dtype=np.int64)
    retained: list[dict[str, object]] = []
    least_conditioned_negative: list[dict[str, object]] = []
    total_minors = 0
    negative_double_count = 0
    robust_negative_double_count = 0
    cases: list[dict[str, object]] = []

    for step in args.steps:
        index = np.arange(args.grid_size, dtype=np.float64)
        for offset_fraction in args.offset_fractions:
            offset = step * offset_fraction
            base = phi(offset + (index[:, None] - index[None, :]) * step)
            case_total = 0
            case_negative = 0
            case_robust_negative = 0

            for start in range(0, subsets.shape[0], args.row_batch_size):
                rows = subsets[start : start + args.row_batch_size]
                matrices = base[
                    rows[:, None, :, None], subsets[None, :, None, :]
                ].reshape(-1, 4, 4)
                determinant, relative = matrix_metrics(matrices)
                finite = np.isfinite(determinant) & np.isfinite(relative)
                finite_indices = np.flatnonzero(finite)
                case_total += int(finite_indices.size)

                negative_indices = np.flatnonzero(finite & (determinant < 0.0))
                case_negative += int(negative_indices.size)
                if negative_indices.size:
                    negative_conditions = condition_numbers(matrices[negative_indices])
                    robust = negative_conditions < args.condition_max
                    case_robust_negative += int(np.count_nonzero(robust))
                    noise_count = min(args.retain, negative_indices.size)
                    noise_partition = np.argpartition(
                        negative_conditions, noise_count - 1
                    )[:noise_count]
                    for noise_position in noise_partition:
                        local_index = negative_indices[noise_position]
                        condition = negative_conditions[noise_position]
                        row_number, column_number = divmod(
                            int(local_index), subsets.shape[0]
                        )
                        row_subset = rows[row_number]
                        column_subset = subsets[column_number]
                        least_conditioned_negative.append(
                            {
                                "step": step,
                                "offset_fraction": offset_fraction,
                                "row_indices": row_subset.tolist(),
                                "column_indices": column_subset.tolist(),
                                "x": (row_subset * step).tolist(),
                                "y": (column_subset * step - offset).tolist(),
                                "determinant": float(determinant[local_index]),
                                "relative": float(relative[local_index]),
                                "condition": float(condition),
                            }
                        )
                    least_conditioned_negative.sort(
                        key=lambda record: float(record["condition"])
                    )
                    del least_conditioned_negative[args.retain :]
                    for local_index, condition in zip(
                        negative_indices[robust], negative_conditions[robust], strict=True
                    ):
                        row_number, column_number = divmod(
                            int(local_index), subsets.shape[0]
                        )
                        row_subset = rows[row_number]
                        column_subset = subsets[column_number]
                        retain_record(
                            retained,
                            {
                                "step": step,
                                "offset_fraction": offset_fraction,
                                "row_indices": row_subset.tolist(),
                                "column_indices": column_subset.tolist(),
                                "x": (row_subset * step).tolist(),
                                "y": (column_subset * step - offset).tolist(),
                                "determinant": float(determinant[local_index]),
                                "normalized": 0.0,
                                "relative": float(relative[local_index]),
                                "condition": float(condition),
                            },
                            args.retain,
                        )

                positive_indices = finite_indices[determinant[finite_indices] >= 0.0]
                if positive_indices.size:
                    count = min(args.retain, positive_indices.size)
                    partition = np.argpartition(relative[positive_indices], count - 1)[:count]
                    selected = positive_indices[partition]
                    selected_conditions = condition_numbers(matrices[selected])
                    for local_index, condition in zip(
                        selected, selected_conditions, strict=True
                    ):
                        if condition >= args.condition_max:
                            continue
                        row_number, column_number = divmod(
                            int(local_index), subsets.shape[0]
                        )
                        row_subset = rows[row_number]
                        column_subset = subsets[column_number]
                        retain_record(
                            retained,
                            {
                                "step": step,
                                "offset_fraction": offset_fraction,
                                "row_indices": row_subset.tolist(),
                                "column_indices": column_subset.tolist(),
                                "x": (row_subset * step).tolist(),
                                "y": (column_subset * step - offset).tolist(),
                                "determinant": float(determinant[local_index]),
                                "normalized": 0.0,
                                "relative": float(relative[local_index]),
                                "condition": float(condition),
                            },
                            args.retain,
                        )

            total_minors += case_total
            negative_double_count += case_negative
            robust_negative_double_count += case_robust_negative
            cases.append(
                {
                    "step": step,
                    "offset_fraction": offset_fraction,
                    "minors": case_total,
                    "negative_double_count": case_negative,
                    "robust_negative_double_count": case_robust_negative,
                }
            )

    verified: list[dict[str, object]] = []
    for record in retained:
        result = verify_candidate(
            np.asarray(record["x"]),
            np.asarray(record["y"]),
            args.denominator,
            args.precision,
        )
        result.update(
            {
                "step": record["step"],
                "offset_fraction": record["offset_fraction"],
                "row_indices": record["row_indices"],
                "column_indices": record["column_indices"],
                "source_determinant_double": record["determinant"],
                "source_relative_double": record["relative"],
                "source_condition_double": record["condition"],
            }
        )
        verified.append(result)

    verified_negative: list[dict[str, object]] = []
    for record in least_conditioned_negative:
        result = verify_candidate(
            np.asarray(record["x"]),
            np.asarray(record["y"]),
            args.denominator,
            args.precision,
        )
        result.update(
            {
                "step": record["step"],
                "offset_fraction": record["offset_fraction"],
                "row_indices": record["row_indices"],
                "column_indices": record["column_indices"],
                "source_determinant_double": record["determinant"],
                "source_relative_double": record["relative"],
                "source_condition_double": record["condition"],
            }
        )
        verified_negative.append(result)

    return {
        "status": "NUMERICAL_TARGET_SELECTION_ONLY",
        "grid_size": args.grid_size,
        "subset_count": int(subsets.shape[0]),
        "steps": args.steps,
        "offset_fractions": args.offset_fractions,
        "total_minors": total_minors,
        "negative_double_count": negative_double_count,
        "robust_negative_double_count": robust_negative_double_count,
        "least_conditioned_negative": least_conditioned_negative,
        "cases": cases,
        "retained": retained,
        "rounded_decimal_checks": verified,
        "least_conditioned_negative_decimal_checks": verified_negative,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--grid-size", type=int, default=12)
    parser.add_argument("--row-batch-size", type=int, default=16)
    parser.add_argument(
        "--steps",
        type=float,
        nargs="+",
        default=[0.01, 0.02, 0.03, 0.04, 0.05, 0.06, 0.08, 0.1, 0.12, 0.15, 0.2],
    )
    parser.add_argument(
        "--offset-fractions", type=float, nargs="+", default=[0.0, 0.1, 0.2, 0.3, 0.4, 0.5]
    )
    parser.add_argument("--condition-max", type=float, default=1.0e12)
    parser.add_argument("--retain", type=int, default=12)
    parser.add_argument("--denominator", type=int, default=1000)
    parser.add_argument("--precision", type=int, default=80)
    return parser.parse_args()


def main() -> None:
    result = run(parse_args())
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
