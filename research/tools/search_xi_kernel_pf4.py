#!/usr/bin/env python3
"""Reproducible numerical target selection for the global Xi-kernel PF4 campaign.

This script is not proof evidence. It searches rational-grid approximations to the
seven-parameter family obtained by fixing x_0 = 0, and verifies promising signs
with Python's high-precision Decimal arithmetic.
"""

from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
import json
import math
from pathlib import Path

import numpy as np


PI = math.pi
DECIMAL_PI = Decimal(
    "3.141592653589793238462643383279502884197169399375105820974944592307816406286"
)


def phi(values: np.ndarray, terms: int = 8) -> np.ndarray:
    """Evaluate Phi(abs(values)) in double precision."""
    u = np.abs(values)
    e4 = np.exp(4.0 * u)
    e5 = np.exp(5.0 * u)
    e9 = np.exp(9.0 * u)
    total = np.zeros_like(u)
    for n in range(1, terms + 1):
        n2 = float(n * n)
        total += (
            2.0 * PI * PI * n2 * n2 * e9 - 3.0 * PI * n2 * e5
        ) * np.exp(-PI * n2 * e4)
    return total


def configurations(parameters: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Decode y_0 and six logarithmic positive gaps."""
    count = parameters.shape[0]
    x = np.zeros((count, 4), dtype=np.float64)
    y = np.empty((count, 4), dtype=np.float64)
    x[:, 1:] = np.cumsum(np.exp(parameters[:, 1:4]), axis=1)
    y[:, 0] = parameters[:, 0]
    y[:, 1:] = y[:, :1] + np.cumsum(np.exp(parameters[:, 4:7]), axis=1)
    return x, y


def vandermonde(points: np.ndarray) -> np.ndarray:
    result = np.ones(points.shape[0], dtype=np.float64)
    for i in range(4):
        for j in range(i + 1, 4):
            result *= points[:, j] - points[:, i]
    return result


def evaluate(parameters: np.ndarray) -> dict[str, np.ndarray]:
    x, y = configurations(parameters)
    matrix = phi(x[:, :, None] - y[:, None, :])
    determinant = np.linalg.det(matrix)
    vdm_scale = vandermonde(x) * vandermonde(y)
    normalized = determinant / vdm_scale
    row_scale = np.prod(np.max(np.abs(matrix), axis=2), axis=1)
    relative = np.full(determinant.shape, np.inf, dtype=np.float64)
    np.divide(determinant, row_scale, out=relative, where=row_scale > 0.0)
    singular_values = np.linalg.svd(matrix, compute_uv=False)
    condition = np.full(matrix.shape[0], np.inf, dtype=np.float64)
    np.divide(
        singular_values[:, 0],
        singular_values[:, -1],
        out=condition,
        where=singular_values[:, -1] > 0.0,
    )
    return {
        "x": x,
        "y": y,
        "matrix": matrix,
        "determinant": determinant,
        "normalized": normalized,
        "relative": relative,
        "condition": condition,
    }


def decimal_phi(value: Decimal, terms: int = 16) -> Decimal:
    u = abs(value)
    e4 = (Decimal(4) * u).exp()
    e5 = (Decimal(5) * u).exp()
    e9 = (Decimal(9) * u).exp()
    total = Decimal(0)
    for n in range(1, terms + 1):
        n2 = Decimal(n * n)
        total += (
            Decimal(2) * DECIMAL_PI * DECIMAL_PI * n2 * n2 * e9
            - Decimal(3) * DECIMAL_PI * n2 * e5
        ) * (-DECIMAL_PI * n2 * e4).exp()
    return total


def decimal_determinant(matrix: list[list[Decimal]]) -> Decimal:
    """Gaussian elimination with partial pivoting over Decimal."""
    work = [row[:] for row in matrix]
    result = Decimal(1)
    for column in range(4):
        pivot = max(range(column, 4), key=lambda row: abs(work[row][column]))
        if work[pivot][column] == 0:
            return Decimal(0)
        if pivot != column:
            work[pivot], work[column] = work[column], work[pivot]
            result = -result
        pivot_value = work[column][column]
        result *= pivot_value
        for row in range(column + 1, 4):
            factor = work[row][column] / pivot_value
            for entry in range(column + 1, 4):
                work[row][entry] -= factor * work[column][entry]
    return result


def round_to_grid(points: np.ndarray, denominator: int) -> list[Decimal]:
    return [
        Decimal(int(round(float(value) * denominator))) / Decimal(denominator)
        for value in points
    ]


def verify_candidate(
    x: np.ndarray, y: np.ndarray, denominator: int, precision: int
) -> dict[str, object]:
    with localcontext() as context:
        context.prec = precision
        rounded_x = round_to_grid(x, denominator)
        rounded_y = round_to_grid(y, denominator)
        matrix = [
            [decimal_phi(rounded_x[i] - rounded_y[j]) for j in range(4)]
            for i in range(4)
        ]
        determinant = decimal_determinant(matrix)
    return {
        "denominator": denominator,
        "x_numerators": [int(value * denominator) for value in rounded_x],
        "y_numerators": [int(value * denominator) for value in rounded_y],
        "strictly_increasing": all(
            rounded_x[index] < rounded_x[index + 1] for index in range(3)
        )
        and all(rounded_y[index] < rounded_y[index + 1] for index in range(3)),
        "determinant_decimal": str(determinant),
    }


def candidate_key(record: dict[str, object]) -> tuple[int, float, float]:
    determinant = float(record["determinant"])
    relative = float(record["relative"])
    condition = float(record["condition"])
    is_robust_negative = determinant < 0.0 and condition < 1.0e12
    if is_robust_negative:
        return (0, relative, condition)
    if condition < 1.0e12:
        return (1, relative, condition)
    if determinant < 0.0:
        return (2, condition, relative)
    return (3, condition, relative)


def run(args: argparse.Namespace) -> dict[str, object]:
    rng = np.random.default_rng(args.seed)
    log_gap_min = math.log(args.gap_min)
    log_gap_max = math.log(args.gap_max)
    retained: list[dict[str, object]] = []
    least_conditioned_negative: list[dict[str, object]] = []
    negative_count = 0
    robust_negative_count = 0
    finite_count = 0

    for _ in range(math.ceil(args.samples / args.batch_size)):
        count = min(args.batch_size, args.samples - finite_count)
        if count <= 0:
            break
        parameters = np.empty((count, 7), dtype=np.float64)
        parameters[:, 0] = rng.uniform(args.offset_min, args.offset_max, count)
        parameters[:, 1:] = rng.uniform(log_gap_min, log_gap_max, (count, 6))
        values = evaluate(parameters)
        finite = np.isfinite(values["determinant"]) & np.isfinite(values["condition"])
        finite_count += count
        negative_count += int(np.count_nonzero(values["determinant"][finite] < 0.0))
        robust_negative_count += int(
            np.count_nonzero(
                (values["determinant"][finite] < 0.0)
                & (values["condition"][finite] < 1.0e12)
            )
        )

        negative_indices = np.flatnonzero(finite & (values["determinant"] < 0.0))
        if negative_indices.size:
            count_negative = min(args.retain, negative_indices.size)
            partition_negative = np.argpartition(
                values["condition"][negative_indices], count_negative - 1
            )[:count_negative]
            for index in negative_indices[partition_negative]:
                least_conditioned_negative.append(
                    {
                        "x": values["x"][index].tolist(),
                        "y": values["y"][index].tolist(),
                        "determinant": float(values["determinant"][index]),
                        "normalized": float(values["normalized"][index]),
                        "relative": float(values["relative"][index]),
                        "condition": float(values["condition"][index]),
                    }
                )
            least_conditioned_negative.sort(
                key=lambda record: float(record["condition"])
            )
            del least_conditioned_negative[args.retain :]

        indices = np.flatnonzero(finite)
        if indices.size:
            category = np.full(indices.size, 3, dtype=np.int8)
            condition = values["condition"][indices]
            determinant = values["determinant"][indices]
            relative = values["relative"][indices]
            reliable = condition < 1.0e12
            negative = determinant < 0.0
            category[negative] = 2
            category[reliable] = 1
            category[reliable & negative] = 0
            score = np.where(category <= 1, relative, condition)
            order = indices[
                np.lexsort(
                    (
                        condition,
                        score,
                        category,
                    )
                )
            ][: args.retain]
            for index in order:
                retained.append(
                    {
                        "x": values["x"][index].tolist(),
                        "y": values["y"][index].tolist(),
                        "determinant": float(values["determinant"][index]),
                        "normalized": float(values["normalized"][index]),
                        "relative": float(values["relative"][index]),
                        "condition": float(values["condition"][index]),
                    }
                )
            retained.sort(key=candidate_key)
            del retained[args.retain :]

    verified: list[dict[str, object]] = []
    for record in retained:
        x = np.asarray(record["x"], dtype=np.float64)
        y = np.asarray(record["y"], dtype=np.float64)
        for denominator in args.denominators:
            result = verify_candidate(x, y, denominator, args.precision)
            result.update(
                {
                    "source_determinant_double": record["determinant"],
                    "source_condition_double": record["condition"],
                }
            )
            verified.append(result)

    verified_negative: list[dict[str, object]] = []
    for record in least_conditioned_negative:
        x = np.asarray(record["x"], dtype=np.float64)
        y = np.asarray(record["y"], dtype=np.float64)
        for denominator in args.denominators:
            result = verify_candidate(x, y, denominator, args.precision)
            result.update(
                {
                    "source_determinant_double": record["determinant"],
                    "source_relative_double": record["relative"],
                    "source_condition_double": record["condition"],
                }
            )
            verified_negative.append(result)

    return {
        "status": "NUMERICAL_TARGET_SELECTION_ONLY",
        "seed": args.seed,
        "samples": args.samples,
        "domain": {
            "offset": [args.offset_min, args.offset_max],
            "gaps": [args.gap_min, args.gap_max],
            "gap_distribution": "log_uniform",
        },
        "negative_double_count": negative_count,
        "robust_negative_double_count": robust_negative_count,
        "least_conditioned_negative": least_conditioned_negative,
        "retained": retained,
        "rounded_decimal_checks": verified,
        "least_conditioned_negative_decimal_checks": verified_negative,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=20260717)
    parser.add_argument("--samples", type=int, default=1_000_000)
    parser.add_argument("--batch-size", type=int, default=50_000)
    parser.add_argument("--offset-min", type=float, default=-0.8)
    parser.add_argument("--offset-max", type=float, default=0.8)
    parser.add_argument("--gap-min", type=float, default=0.002)
    parser.add_argument("--gap-max", type=float, default=0.5)
    parser.add_argument("--retain", type=int, default=12)
    parser.add_argument("--precision", type=int, default=80)
    parser.add_argument(
        "--denominators", type=int, nargs="+", default=[100, 200, 500, 1000]
    )
    parser.add_argument("--output", type=Path)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    result = run(args)
    rendered = json.dumps(result, indent=2, sort_keys=True)
    if args.output is None:
        print(rendered)
    else:
        args.output.write_text(rendered + "\n", encoding="ascii")


if __name__ == "__main__":
    main()
