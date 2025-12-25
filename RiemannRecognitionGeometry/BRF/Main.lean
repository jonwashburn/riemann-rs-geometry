/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

# BRF Route: Main Hub

This module imports all components of the Bounded Real Function (BRF) / Schur-Herglotz route
for the Riemann Hypothesis, as described in `Riemann-Christmas.tex`.

## Proof Architecture

The BRF route establishes:

1. **Cayley Transform** (`Cayley.lean`):
   - `cayley z = (z - 1) / (z + 1)` maps Re(z) ≥ 0 to unit disk
   - `theta J = cayley (2 * J)` is the paper's scaled version

2. **Phase & Wedge** (`Phase.lean`, `Wedge.lean`):
   - `phase w = exp(i w)` is the unimodular phase function
   - Wedge bound `|w| ≤ π/2` implies `Re(phase w) ≥ 0`
   - This feeds into the Cayley transform

3. **Essential Oscillation** (`Oscillation.lean`):
   - `oscOn w s = essSup - essInf` on set s
   - Foundation for the local-to-global argument

4. **Local-to-Global Wedge** (`LocalToGlobal.lean`):
   - Key theorem: uniform local oscillation bounds → global wedge after rotation
   - `exists_shift_ae_abs_sub_le_of_oscOn_Icc_exhaustion`

5. **Stieltjes Measure** (`Stieltjes.lean`):
   - `stieltjesNeg w` defines measure for antitone phase w
   - Mass on interval = phase drop

6. **Window → Oscillation Bridge** (`WindowBridge.lean`):
   - Plateau extraction: window bound → Stieltjes mass → oscillation
   - `oscOn_Icc_le_div_of_window_lintegral_bound`

7. **Certificate Windows** (`CertificateWindow.lean`):
   - Flat-top and Poisson-plateau window constructions
   - Instantiations for Whitney intervals

## Usage

Import this module to get access to the complete BRF route:

```lean
import RiemannRecognitionGeometry.BRF.Main
```

Then use theorems like:
- `norm_cayley_le_one_of_re_nonneg`: Cayley maps to disk
- `ae_norm_theta_phase_le_one_of_ae_abs_le_pi_mul`: wedge → Schur
- `exists_shift_ae_abs_sub_le_of_oscOn_Icc_exhaustion`: local → global
- `oscOn_Icc_le_div_of_window_lintegral_bound`: B1 bridge
-/

import RiemannRecognitionGeometry.BRF.Cayley
import RiemannRecognitionGeometry.BRF.Phase
import RiemannRecognitionGeometry.BRF.Wedge
import RiemannRecognitionGeometry.BRF.Oscillation
import RiemannRecognitionGeometry.BRF.LocalToGlobal
import RiemannRecognitionGeometry.BRF.Stieltjes
import RiemannRecognitionGeometry.BRF.WindowBridge
import RiemannRecognitionGeometry.BRF.CertificateWindow
import RiemannRecognitionGeometry.BRF.Bridge

namespace RiemannRecognitionGeometry
namespace BRF

/-!
## Route Status

All theorems in the BRF route are **fully proven** with no `sorry`.

This provides a complete algebraic/measure-theoretic infrastructure for the
Riemann Hypothesis via the Schur/Herglotz approach from `Riemann-Christmas.tex`.

### Key Exports

The BRF route provides these core capabilities:

- **Cayley**: `norm_cayley_le_one_of_re_nonneg` - right half-plane maps to closed unit disk
- **Schur**: `norm_theta_le_one_of_re_nonneg` - paper-compatible theta transform
- **Wedge → Positivity**: `re_phase_nonneg_of_abs_le_pi_div_two` - phase wedge implies nonnegative real part
- **a.e. Schur**: `ae_norm_theta_phase_le_one_of_ae_abs_le_pi_mul` - wedge bound gives a.e. Schur property
- **Local → Global**: `exists_shift_ae_abs_sub_le_of_oscOn_Icc_exhaustion` - oscillation on exhaustion gives global wedge
- **Oscillation control**: `oscOn_Icc_le_drop_of_antitone` - antitone phase has oscillation ≤ drop
- **B1 Bridge**: `oscOn_Icc_le_div_of_window_lintegral_bound` - window lintegral bound → oscillation bound
- **Whitney instantiation**: `oscOn_Icc_whitney_le_mul_L_of_flatTop` - flat-top window on Whitney intervals

### Remaining analytic work

To complete RH via this route, one needs to:
1. Bound the oscillation of `log|ξ|` on Whitney intervals (analytic input)
2. Apply the local-to-global wedge lemma
3. Use the Cayley/Schur machinery to derive a contradiction from any off-critical zero

This analytic work is separate from the algebraic infrastructure formalized here.
-/

end BRF
end RiemannRecognitionGeometry
