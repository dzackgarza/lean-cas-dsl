/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Syntax
public import CasCatalogue.Leaves.Foundation.Catalogue
public import CasCatalogue.Leaves.Algebra.Catalogue

@[expose] public section

/-!
# Magmas cluster — least-host ownership

Owns Magmas and the magma classifiers Associative / Commutative / Unital / Inverse,
plus standard names Semigroups / Monoids / Groups as expressions.
-/

namespace CasCatalogue.Algebra.Catalogue.Magmas


open CasCatalogue
/-- Magmas := total(BinaryOperation on Sets). -/
def Magmas : CategoryExpr := .classifierTotal ClassifierId.setsBinaryOperation

def Associative : ClassifierId := ClassifierId.magmasAssociative
def Commutative : ClassifierId := ClassifierId.magmasCommutative
def Unital : ClassifierId := ClassifierId.magmasUnital
def Inverse : ClassifierId := ClassifierId.magmasInverse

/- These named categories remain atoms until their pullback realizations exist. -/
/-- Semigroups are the associative magmas: the total of the associativity classifier (CC-PROP). -/
def Semigroups : CategoryExpr := .classifierTotal ClassifierId.magmasAssociative
def Monoids : CategoryExpr := .atom CategoryId.monoids
def Groups : CategoryExpr := .atom CategoryId.groups

def AdditiveMagmas : CategoryExpr :=
  .atom CategoryId.additiveMagmas

def AdditiveSemigroups : CategoryExpr :=
  .atom CategoryId.additiveSemigroups

def AdditiveMonoids : CategoryExpr :=
  .atom CategoryId.additiveMonoids

def AdditiveGroups : CategoryExpr :=
  .atom CategoryId.additiveGroups

end CasCatalogue.Algebra.Catalogue.Magmas
