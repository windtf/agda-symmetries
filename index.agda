module index where

--------------------------------
-- paper artifacts
-------------------------------
import types25pp
--------------------------------

--------------------------------
-- library modules
--------------------------------

-- universal algebra
import Cubical.Structures.Sig
import Cubical.Structures.Str
import Cubical.Structures.Eq
import Cubical.Structures.Coh

-- free algebras
import Cubical.Structures.Free

---------------------------------
-- free monoids on sets
import Cubical.Structures.Set.Mon.Free
import Cubical.Structures.Set.Mon.List
import Cubical.Structures.Set.Mon.Array

---------------------------------
-- free commutative monoids on sets
import Cubical.Structures.Set.CMon.Free
import Cubical.Structures.Set.CMon.SList
import Cubical.Structures.Set.CMon.CList
import Cubical.Structures.Set.CMon.PList
import Cubical.Structures.Set.CMon.QFreeMon
import Cubical.Structures.Set.CMon.Bag

---------------------------------
-- free monoidal groupoids on groupoids
import Cubical.Structures.Gpd.Mon.Free
import Cubical.Structures.Gpd.Mon.List

---------------------------------
-- free symmetric monoidal groupoids on groupoids
import Cubical.Structures.Gpd.SMon.Free
import Cubical.Structures.Gpd.SMon.SList

---------------------------------
-- equivalence between sorting functions and orders
import Cubical.Structures.Set.CMon.SList.Sort
---------------------------------

-- combinatorics
import Cubical.Structures.Set.CMon.SList.Seely

-- (un)useful experiments
import Experiments.Norm

---------------------------------
-- an exhaustive list of all modules:
import Everything
