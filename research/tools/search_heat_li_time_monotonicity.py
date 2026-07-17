#!/usr/bin/env python3
"""Numerical falsification gate for actual-theta heat-Li time monotonicity.

This script is target-selection tooling, never proof evidence. It evaluates the
time derivative through the formal identity d_t log(F) = (d_t F) / F, avoiding
finite differences between nearby Li values.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from typing import Iterable

import mpmath as mp


@dataclass(frozen=True)
class QuadratureNode:
    u: mp.mpf
    weighted_phi: mp.mpf


def phi(u: mp.mpf, tolerance: mp.mpf) -> mp.mpf:
    e4 = mp.exp(4 * u)
    e5 = mp.exp(5 * u)
    e9 = mp.exp(9 * u)
    total = mp.mpf("0")
    for n in range(1, 65):
        n2 = mp.mpf(n * n)
        term = (
            2 * mp.pi**2 * n2**2 * e9 - 3 * mp.pi * n2 * e5
        ) * mp.exp(-mp.pi * n2 * e4)
        total += term
        if n >= 4 and abs(term) <= tolerance * max(mp.mpf("1"), abs(total)):
            break
    return total


def tanh_sinh_nodes(
    cutoff: mp.mpf, step_denominator: int, half_count: int, tolerance: mp.mpf
) -> list[QuadratureNode]:
    step = mp.mpf(1) / step_denominator
    result: list[QuadratureNode] = []
    for index in range(-half_count, half_count + 1):
        x = index * step
        inner = (mp.pi / 2) * mp.sinh(x)
        y = mp.tanh(inner)
        u = (cutoff / 2) * (1 + y)
        jacobian = (cutoff / 2) * (mp.pi / 2) * mp.cosh(x) / mp.cosh(inner) ** 2
        weight = step * jacobian
        if weight == 0:
            continue
        result.append(QuadratureNode(u=u, weighted_phi=weight * phi(u, tolerance)))
    return result


def compose_at_one_over_one_sub_z(derivatives: list[mp.mpf]) -> list[mp.mpf]:
    """Compose the Taylor series at s=1 with s=1/(1-z)."""
    degree = len(derivatives) - 1
    taylor = [derivatives[k] / mp.factorial(k) for k in range(degree + 1)]
    result = [mp.mpf("0") for _ in range(degree + 1)]
    result[0] = taylor[0]
    for power in range(1, degree + 1):
        for degree_z in range(power, degree + 1):
            result[degree_z] += taylor[power] * mp.binomial(
                degree_z - 1, power - 1
            )
    return result


def inverse_series(series: list[mp.mpf]) -> list[mp.mpf]:
    degree = len(series) - 1
    result = [mp.mpf("0") for _ in range(degree + 1)]
    result[0] = 1 / series[0]
    for index in range(1, degree + 1):
        result[index] = -sum(
            series[k] * result[index - k] for k in range(1, index + 1)
        ) / series[0]
    return result


def multiply_series(left: list[mp.mpf], right: list[mp.mpf]) -> list[mp.mpf]:
    degree = min(len(left), len(right)) - 1
    return [
        sum(left[k] * right[index - k] for k in range(index + 1))
        for index in range(degree + 1)
    ]


def li_values_and_time_derivatives(
    derivatives: list[mp.mpf], time_derivatives: list[mp.mpf]
) -> tuple[list[mp.mpf], list[mp.mpf]]:
    f_series = compose_at_one_over_one_sub_z(derivatives)
    ft_series = compose_at_one_over_one_sub_z(time_derivatives)
    inverse = inverse_series(f_series)
    ratio = multiply_series(ft_series, inverse)
    degree = len(derivatives) - 1

    li_values: list[mp.mpf] = []
    li_time_derivatives: list[mp.mpf] = []
    for classical_index in range(1, degree + 1):
        log_coefficient_times_index = sum(
            (k + 1) * f_series[k + 1] * inverse[classical_index - 1 - k]
            for k in range(classical_index)
        )
        li_values.append(log_coefficient_times_index)
        li_time_derivatives.append(classical_index * ratio[classical_index])
    return li_values, li_time_derivatives


def theta_derivatives(
    nodes: list[QuadratureNode], time: mp.mpf, max_index: int
) -> tuple[list[mp.mpf], list[mp.mpf]]:
    degree = max_index + 1
    derivatives = [mp.mpf("0") for _ in range(degree + 1)]
    time_derivatives = [mp.mpf("0") for _ in range(degree + 1)]
    for node in nodes:
        u = node.u
        base = node.weighted_phi * mp.exp(time * u**2)
        even_factor = mp.cosh(u)
        odd_factor = mp.sinh(u)
        power = mp.mpf("1")
        two_power = mp.mpf("1")
        for order in range(degree + 1):
            hyperbolic = even_factor if order % 2 == 0 else odd_factor
            summand = 8 * two_power * base * power * hyperbolic
            derivatives[order] += summand
            time_derivatives[order] += summand * u**2
            power *= u
            two_power *= 2
    return derivatives, time_derivatives


def finite_cosh_derivatives(
    atoms: list[tuple[mp.mpf, mp.mpf]], time: mp.mpf, max_index: int
) -> tuple[list[mp.mpf], list[mp.mpf]]:
    degree = max_index + 1
    derivatives = [mp.mpf("0") for _ in range(degree + 1)]
    time_derivatives = [mp.mpf("0") for _ in range(degree + 1)]
    for location, coefficient in atoms:
        heated_coefficient = coefficient * mp.exp(time * location**2) / mp.cosh(
            location
        )
        power = mp.mpf("1")
        two_power = mp.mpf("1")
        for order in range(degree + 1):
            hyperbolic = mp.cosh(location) if order % 2 == 0 else mp.sinh(location)
            summand = heated_coefficient * two_power * power * hyperbolic
            derivatives[order] += summand
            time_derivatives[order] += summand * location**2
            power *= location
            two_power *= 2
    return derivatives, time_derivatives


def default_times() -> list[mp.mpf]:
    uniform = [mp.mpf(-4) + mp.mpf(index) / 10 for index in range(41)]
    geometric = [-mp.power(2, exponent) for exponent in range(-8, 5)]
    return sorted(set(uniform + geometric + [mp.mpf("0")]))


def serialize(value: mp.mpf, digits: int = 30) -> str:
    return mp.nstr(value, digits, strip_zeros=False)


def scan_family(
    family: str,
    times: Iterable[mp.mpf],
    max_index: int,
    evaluator,
) -> dict[str, object]:
    minimum = None
    minimum_record = None
    negatives: list[dict[str, object]] = []
    per_index = [None for _ in range(max_index + 1)]
    first_index_minimum = None
    first_value_calibration_error = mp.mpf("0")
    first_slope_calibration_error = mp.mpf("0")

    for time in times:
        derivatives, time_derivatives = evaluator(time, max_index)
        values, slopes = li_values_and_time_derivatives(
            derivatives, time_derivatives
        )
        direct_first_value = derivatives[1] / derivatives[0]
        direct_first_slope = (
            time_derivatives[1] * derivatives[0]
            - derivatives[1] * time_derivatives[0]
        ) / derivatives[0] ** 2
        first_value_calibration_error = max(
            first_value_calibration_error, abs(values[0] - direct_first_value)
        )
        first_slope_calibration_error = max(
            first_slope_calibration_error, abs(slopes[0] - direct_first_slope)
        )
        for index, (value, slope) in enumerate(zip(values, slopes, strict=True)):
            record = {
                "index": index,
                "time": serialize(time),
                "value": serialize(value),
                "time_derivative": serialize(slope),
            }
            if minimum is None or slope < minimum:
                minimum = slope
                minimum_record = record
            if per_index[index] is None or slope < per_index[index][0]:
                per_index[index] = (slope, record)
            if index == 0 and (
                first_index_minimum is None or slope < first_index_minimum
            ):
                first_index_minimum = slope
            if slope < 0:
                negatives.append(record)

    return {
        "family": family,
        "minimum": minimum_record,
        "first_index_minimum_derivative": serialize(first_index_minimum),
        "first_index_calibration": {
            "value_formula": "F'(1)/F(1)",
            "time_derivative_formula":
                "(partial_t F'(1)*F(1)-F'(1)*partial_t F(1))/F(1)^2",
            "maximum_value_abs_error": serialize(first_value_calibration_error),
            "maximum_time_derivative_abs_error": serialize(
                first_slope_calibration_error
            ),
        },
        "negative_count": len(negatives),
        "negatives": negatives[:32],
        "per_index_minimum": [record for _, record in per_index],
    }


def run(args: argparse.Namespace) -> dict[str, object]:
    mp.mp.dps = args.dps
    tolerance = mp.power(10, -(args.dps - 15))
    cutoff = mp.mpf(args.cutoff)
    nodes = tanh_sinh_nodes(
        cutoff, args.step_denominator, args.half_count, tolerance
    )
    times = default_times()
    theta = scan_family(
        "actual_theta",
        times,
        args.max_index,
        lambda time, max_index: theta_derivatives(nodes, time, max_index),
    )

    log_two = mp.log(2)
    audit_atoms = [
        (log_two, mp.mpf(1) / 8),
        (10 * log_two, mp.mpf(7) / 8),
    ]
    finite_mixture = scan_family(
        "positive_two_atom_cosh",
        times,
        args.max_index,
        lambda time, max_index: finite_cosh_derivatives(
            audit_atoms, time, max_index
        ),
    )

    return {
        "status": "NUMERICAL_TARGET_SELECTION_ONLY",
        "precision_digits": args.dps,
        "max_project_index": args.max_index,
        "time_count": len(times),
        "time_min": serialize(min(times)),
        "time_max": serialize(max(times)),
        "quadrature": {
            "method": "fixed_tanh_sinh",
            "cutoff": args.cutoff,
            "step_denominator": args.step_denominator,
            "half_count": args.half_count,
            "node_count": len(nodes),
            "theta_term_tolerance": serialize(tolerance),
        },
        "actual_theta": theta,
        "finite_mixture_control": finite_mixture,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dps", type=int, default=80)
    parser.add_argument("--max-index", type=int, default=31)
    parser.add_argument("--cutoff", default="3")
    parser.add_argument("--step-denominator", type=int, default=32)
    parser.add_argument("--half-count", type=int, default=160)
    return parser.parse_args()


def main() -> None:
    print(json.dumps(run(parse_args()), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
