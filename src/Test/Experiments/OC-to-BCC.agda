{-# OPTIONS --sized-types --guardedness #-}

module Test.Experiments.OC-to-BCC where

open import Data.Bool using (true; false)
open import Data.List using (_∷_; [])
open import Data.String using (String; _++_; unlines)
open import Size using (∞)
open import IO using (putStrLn; _>>_)

open import Lang.OC
open import Lang.BCC
open import Translation.Translation using (expr)
open import Translation.OC-to-BCC using (translate)
open import SemanticDomain using (showVariant)

open import Test.Experiment
open import Test.Example
open import Test.Examples.OC

-- Configure an option calculus expression with an all-yes and an all-no config and print the resulting variants.
exp-oc-to-bcc : Experiment (WFOC ∞ String)
name exp-oc-to-bcc = "Translate OC expression to BCC"
run  exp-oc-to-bcc (name example: oc) = do
  putStrLn (show-wfoc oc)
  putStrLn "  ↓  "
  putStrLn (Lang.BCC.show (expr (translate oc)))
