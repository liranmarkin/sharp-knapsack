# #Knapsack: A Faster FPTAS

This repository accompanies the paper **"A Faster FPTAS for #Knapsack"** by Pawel Gawrychowski, Liran Markin, and Oren Weimann, published at **ICALP 2018** ([DOI: 10.4230/LIPIcs.ICALP.2018.64](https://doi.org/10.4230/LIPIcs.ICALP.2018.64)).

The paper is included here: [`faster-fptas-knapsack.pdf`](faster-fptas-knapsack.pdf).

## The problem

Given a set W = {w1, ..., wn} of non-negative integer weights and an integer C, the #Knapsack problem asks to count the number of distinct subsets of W whose total weight is at most C. It is the counting version of the classical Knapsack problem and is #P-hard, yet it admits a deterministic approximation scheme - a rarity among #P-hard counting problems.

## The result

A deterministic FPTAS for #Knapsack running in

O(n^2.5 eps^-1.5 log(n eps^-1) log(n eps)) time,

improving on the previous best deterministic O(n^3 eps^-1 log(n eps^-1)) algorithm and, for constant eps, closing the gap between the O~(n^2.5) randomized and O~(n^3) deterministic running times. The paper also gives a faster FPTAS for the integer (multiset) version of the problem.

The key idea: instead of recursing on all but the last item as in the standard recurrence, the algorithm recurses in the middle and merges the two sub-solutions with convolution, extending the technique of K-approximation sets and functions.

## Planned

- A reference implementation of the algorithm.
- A formal verification of its correctness.
