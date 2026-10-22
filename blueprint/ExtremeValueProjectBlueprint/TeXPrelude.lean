import Verso
import VersoManual
import VersoBlueprint

open Informal

-- TeX macros shared by all chapters (formerly `blueprint/src/macros/common.tex`).
-- `\def` is used instead of `\newcommand` so that macros which KaTeX already
-- provides (such as `\R`) are redefined instead of raising an error.
tex_prelude r#"
\def\Z{\mathbb{Z}}
\def\bZ{\Z}
\def\N{\mathbb{N}}
\def\bN{\N}
\def\Q{\mathbb{Q}}
\def\bQ{\Q}
\def\R{\mathbb{R}}
\def\bR{\R}
\def\C{\mathbb{C}}
\def\bC{\C}
\def\Zpos{\Z_{>0}}
\def\Znn{\Z_{\ge 0}}
\def\Npos{\N_{+}}

\def\PR{\mathsf{P}}
\def\EX{\mathsf{E}}

\def\indof#1{\mathbb{I}_{{#1}}}
\def\PRmeas{\mu}

\def\eps{\varepsilon}

\def\oo{\mathfrak{o}}
\def\OO{\mathcal{O}}

\def\Aut{\operatorname{Aut}}
\def\Hom{\operatorname{Hom}}
\def\GL{\operatorname{GL}}
\def\PGL{\operatorname{PGL}}
\def\PSL{\operatorname{PSL}}
\def\SL{\operatorname{SL}}
\def\tr{\operatorname{tr}}
\def\id{\operatorname{id}}
\def\dmn{\operatorname{dim}}

\def\set#1{\left\{ #1 \right\}}

\def\lcinv#1{{#1}^{\rightarrow 1}}
\def\rcinv#1{{#1}^{\leftarrow 1}}

\def\AffOf#1{\mathrm{Aff}_{#1}}
\def\AffR{\AffOf{\R}}
\def\OriAffR{\mathrm{Aff}^+_{\R}}

\def\tendsinlaw{\overset{\mathrm{d}}{\longrightarrow}}

\def\Gumbel{\mathrm{Gumbel}}
\def\Weibull{\mathrm{Weibull}}
\def\Frechet{\mathrm{Fréchet}}
\def\GumbelCDF{\Lambda}
\def\WeibullCDF#1{\Psi_{#1}}
\def\FrechetCDF#1{\Phi_{#1}}

\def\extendcdf#1{\widetilde{#1}}
\def\oneDivOneSub#1{\frac{\mathbf{1}}{\mathbf{1}-\extendcdf{#1}}}
\def\oneDivNegLog#1{\frac{\mathbf{1}}{\widetilde{\log} \big( 1 / \extendcdf{#1} \big)}}

\def\ud{\mathrm{d}}
\def\der#1{\frac{\ud}{\ud #1}}
\def\dder#1{\frac{\ud^2}{\ud {#1}^2}}

\def\Leb{\Lambda}
"#
