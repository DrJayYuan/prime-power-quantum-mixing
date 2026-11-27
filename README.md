# Exact uniform mixing on odd-prime-power quantum paths

[Research manuscript (PDF)](paper/prime-power-mixing.pdf) · [Editable manuscript](paper/prime-power-mixing.html) · [Lean proofs](PrimePowerMixing.lean) · [Build checks](../../actions)

The manuscript proves that for a uniform quantum chain with $N=p^a-1$ sites, where $p$ is an odd prime and $a\ge2$, a finite probability law on nonnegative integer readout times makes every transition probability exactly $1/N$ after averaging. The same law works for every initial site. It covers the odd-prime-power family left unresolved by [Kang's 2026 preprint](https://arxiv.org/abs/2609.14463).

## 中文摘要

对 $N=p^a-1$ 个格点的均匀量子链，其中 $p$ 是奇素数、$a\ge2$，手稿证明存在一组有限的非负整数测量时刻及其抽样概率。每次实验独立抽一个时刻测量一次。无论粒子从哪个格点出发，任意格点最终被测到的平均概率都精确等于 $1/N$。对 8 格点链，手稿还给出一套有 17 个时刻的具体方案。

## Lean 4 coverage / 形式化范围

| File | Checked result |
| --- | --- |
| [Relations](PrimePowerMixing/Relations.lean) | A vanishing rational polynomial of degree below a prime power has identical coefficient blocks at a primitive root of that order. |
| [EightSiteRelations](PrimePowerMixing/EightSiteRelations.lean) | The four even-mode energies for the eight-site chain have just one independent rational relation. |
| [Moments](PrimePowerMixing/Moments.lean) | The without-replacement correlation and exact positive weights for the two block laws and a zero-moment component. |
| [EightSites](PrimePowerMixing/EightSites.lean) | An explicit 72-outcome phase ensemble with all 64 cosine moments verified, including its block constraint and the real trigonometric interpretation. |
| [Readout](PrimePowerMixing/Readout.lean) | The finite spectral readout expansion and the implication from target parity moments and the two sine-basis identities to uniformity. |
| [TimeTransfer](PrimePowerMixing/TimeTransfer.lean) | A convex-geometric transfer theorem from interior limiting moments to a positive finite law on integer times, with the Carathéodory support bound. |

The complete chain theorem is proved in the manuscript. Completing its Lean formalization requires the general sampling-law construction, the sine-basis identities, and proofs of the orbit-density and interior hypotheses for these chains. The concrete 17-time schedule uses a separate interval-arithmetic certificate.

Lean 已核验上表中的引理，以及八格点相位分布的全部 64 个余弦矩。一般情形的抽样分布、正弦谱基恒等式、整数时间轨道稠密性及其凸包内部条件，仍需接成 Lean 主定理。17 个实际测量时刻的权重由独立的 Python 区间算术脚本检验。

## Reproduce / 复现

Use the pinned Lean 4.28.0 toolchain and mathlib revision in this repository. With [elan](https://github.com/leanprover/elan) on the path, run:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The [axiom report](Audit.lean) prints the foundations used by the principal lemmas. For the eight-site integer readout schedule:

```sh
python -m pip install numpy mpmath
python code/check_p8.py
```

The script certifies that every exact weight exceeds 0.02022. It also reproduces the site-basis cross-check for all 64 transition probabilities.
