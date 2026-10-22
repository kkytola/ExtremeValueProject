import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import ExtremeValueProjectBlueprint.TeXPrelude
import ExtremeValueProjectBlueprint.Chapters.Cdf
import ExtremeValueProjectBlueprint.Chapters.ExtremeValueDistributions
import ExtremeValueProjectBlueprint.Chapters.Classification
import ExtremeValueProjectBlueprint.Chapters.CdfConvergence
import ExtremeValueProjectBlueprint.Chapters.Transforms
import ExtremeValueProjectBlueprint.Chapters.OneParameterAffine
import ExtremeValueProjectBlueprint.Chapters.Types
import ExtremeValueProjectBlueprint.Chapters.LcInverse
import ExtremeValueProjectBlueprint.Chapters.CauchyEqn

open Verso.Genre Manual Informal

#doc (Manual) "Extreme Value Distribution Project" =>

%%%
authors := ["Kalle Kytölä"]
%%%

This is a blueprint for a project which forms a part of the course
_MS-EV0029 Introduction to Formalized Mathematics in Lean_
at Aalto University, running from February to June, 2025.
The goal is to formalize the Fisher-Tippett-Gnedenko theorem,
classifying univariate extreme value distributions.
Contributions are welcome by course participants!

*WARNING: The blueprint is still work in progress!*
Contributions by the course participants
to improve the blueprint and add details
(which are helpful for formalization) are very welcome!

{include 0 ExtremeValueProjectBlueprint.Chapters.Cdf}
{include 0 ExtremeValueProjectBlueprint.Chapters.ExtremeValueDistributions}
{include 0 ExtremeValueProjectBlueprint.Chapters.Classification}
{include 0 ExtremeValueProjectBlueprint.Chapters.CdfConvergence}
{include 0 ExtremeValueProjectBlueprint.Chapters.Transforms}
{include 0 ExtremeValueProjectBlueprint.Chapters.OneParameterAffine}
{include 0 ExtremeValueProjectBlueprint.Chapters.Types}
{include 0 ExtremeValueProjectBlueprint.Chapters.LcInverse}
{include 0 ExtremeValueProjectBlueprint.Chapters.CauchyEqn}

{blueprint_graph}
{blueprint_summary}
