import TransposeFree

namespace HGP13.TransposeCertificate
open HGP13.TransposeFree
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def row000 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked000 : ∀ y : BitVec 7, fastPotential 0 y = true →
    check 0 y (row000 y) = true := by decide

def row001 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked001 : ∀ y : BitVec 7, fastPotential 1 y = true →
    check 1 y (row001 y) = true := by decide

def row002 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked002 : ∀ y : BitVec 7, fastPotential 2 y = true →
    check 2 y (row002 y) = true := by decide

def row003 (y : BitVec 7) : Cut := match y.toNat with
  | 12 => ⟨[0,1,2,3,4,8,12,16,17,21,32,64,67,96,104],62⟩
  | 54 => ⟨[0,1,2,3,4,8,16,17,21,32,64,67,96,104],62⟩
  | 58 => ⟨[0,1,2,3,4,8,16,17,21,32,64,67,96,104],62⟩
  | _ => default
theorem checked003 : ∀ y : BitVec 7, fastPotential 3 y = true →
    check 3 y (row003 y) = true := by decide

def row004 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked004 : ∀ y : BitVec 7, fastPotential 4 y = true →
    check 4 y (row004 y) = true := by decide

def row005 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked005 : ∀ y : BitVec 7, fastPotential 5 y = true →
    check 5 y (row005 y) = true := by decide

def row006 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked006 : ∀ y : BitVec 7, fastPotential 6 y = true →
    check 6 y (row006 y) = true := by decide

def row007 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked007 : ∀ y : BitVec 7, fastPotential 7 y = true →
    check 7 y (row007 y) = true := by decide

def row008 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked008 : ∀ y : BitVec 7, fastPotential 8 y = true →
    check 8 y (row008 y) = true := by decide

def row009 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked009 : ∀ y : BitVec 7, fastPotential 9 y = true →
    check 9 y (row009 y) = true := by decide

def row010 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked010 : ∀ y : BitVec 7, fastPotential 10 y = true →
    check 10 y (row010 y) = true := by decide

def row011 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked011 : ∀ y : BitVec 7, fastPotential 11 y = true →
    check 11 y (row011 y) = true := by decide

def row012 (y : BitVec 7) : Cut := match y.toNat with
  | 3 => ⟨[0,1,2,3,4,8,12,16,17,21,32,64,67,96,104],62⟩
  | 35 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104],62⟩
  | 43 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104],62⟩
  | 65 => ⟨[0,1,2,4,8,12,16,17,21,32,64,65,67,96,104],62⟩
  | 66 => ⟨[0,1,2,4,8,12,16,17,21,32,64,66,67,96,104],62⟩
  | 71 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104],62⟩
  | 75 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104],62⟩
  | 79 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104],62⟩
  | 82 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104],62⟩
  | 83 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104],62⟩
  | 86 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104],62⟩
  | 99 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104],62⟩
  | 113 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104,113],62⟩
  | 125 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104,125],62⟩
  | _ => default
theorem checked012 : ∀ y : BitVec 7, fastPotential 12 y = true →
    check 12 y (row012 y) = true := by decide

def row013 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked013 : ∀ y : BitVec 7, fastPotential 13 y = true →
    check 13 y (row013 y) = true := by decide

def row014 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked014 : ∀ y : BitVec 7, fastPotential 14 y = true →
    check 14 y (row014 y) = true := by decide

def row015 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked015 : ∀ y : BitVec 7, fastPotential 15 y = true →
    check 15 y (row015 y) = true := by decide

def row016 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked016 : ∀ y : BitVec 7, fastPotential 16 y = true →
    check 16 y (row016 y) = true := by decide

def row017 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked017 : ∀ y : BitVec 7, fastPotential 17 y = true →
    check 17 y (row017 y) = true := by decide

def row018 (y : BitVec 7) : Cut := match y.toNat with
  | 43 => ⟨[0,1,2,4,8,16,17,18,21,32,50,64,96,104],62⟩
  | 86 => ⟨[0,1,2,4,8,16,17,18,21,32,50,64,96,104],62⟩
  | 125 => ⟨[0,1,2,4,8,16,17,18,21,32,50,64,96,104,125],62⟩
  | _ => default
theorem checked018 : ∀ y : BitVec 7, fastPotential 18 y = true →
    check 18 y (row018 y) = true := by decide

def row019 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked019 : ∀ y : BitVec 7, fastPotential 19 y = true →
    check 19 y (row019 y) = true := by decide

def row020 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked020 : ∀ y : BitVec 7, fastPotential 20 y = true →
    check 20 y (row020 y) = true := by decide

def row021 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked021 : ∀ y : BitVec 7, fastPotential 21 y = true →
    check 21 y (row021 y) = true := by decide

def row022 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked022 : ∀ y : BitVec 7, fastPotential 22 y = true →
    check 22 y (row022 y) = true := by decide

def row023 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked023 : ∀ y : BitVec 7, fastPotential 23 y = true →
    check 23 y (row023 y) = true := by decide

def row024 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked024 : ∀ y : BitVec 7, fastPotential 24 y = true →
    check 24 y (row024 y) = true := by decide

def row025 (y : BitVec 7) : Cut := match y.toNat with
  | 43 => ⟨[0,1,2,4,8,16,17,21,25,32,64,96,104],62⟩
  | _ => default
theorem checked025 : ∀ y : BitVec 7, fastPotential 25 y = true →
    check 25 y (row025 y) = true := by decide

def row026 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked026 : ∀ y : BitVec 7, fastPotential 26 y = true →
    check 26 y (row026 y) = true := by decide

def row027 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked027 : ∀ y : BitVec 7, fastPotential 27 y = true →
    check 27 y (row027 y) = true := by decide

def row028 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked028 : ∀ y : BitVec 7, fastPotential 28 y = true →
    check 28 y (row028 y) = true := by decide

def row029 (y : BitVec 7) : Cut := match y.toNat with
  | 35 => ⟨[0,1,2,4,8,16,17,21,29,32,64,96,104],62⟩
  | _ => default
theorem checked029 : ∀ y : BitVec 7, fastPotential 29 y = true →
    check 29 y (row029 y) = true := by decide

def row030 (y : BitVec 7) : Cut := match y.toNat with
  | 35 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 82 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 113 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | _ => default
theorem checked030 : ∀ y : BitVec 7, fastPotential 30 y = true →
    check 30 y (row030 y) = true := by decide

def row031 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked031 : ∀ y : BitVec 7, fastPotential 31 y = true →
    check 31 y (row031 y) = true := by decide

def row032 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked032 : ∀ y : BitVec 7, fastPotential 32 y = true →
    check 32 y (row032 y) = true := by decide

def row033 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked033 : ∀ y : BitVec 7, fastPotential 33 y = true →
    check 33 y (row033 y) = true := by decide

def row034 (y : BitVec 7) : Cut := match y.toNat with
  | 43 => ⟨[0,1,2,4,8,16,17,21,32,34,50,64,96,104],62⟩
  | 86 => ⟨[0,1,2,4,8,16,17,21,32,34,50,64,96,104],62⟩
  | 125 => ⟨[0,1,2,4,8,16,17,21,32,34,50,64,96,104,125],62⟩
  | _ => default
theorem checked034 : ∀ y : BitVec 7, fastPotential 34 y = true →
    check 34 y (row034 y) = true := by decide

def row035 (y : BitVec 7) : Cut := match y.toNat with
  | 12 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104],62⟩
  | 29 => ⟨[0,1,2,4,8,16,17,21,29,32,64,96,104],62⟩
  | 30 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 43 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 46 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 47 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 54 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 58 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 60 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 63 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 86 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 94 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 125 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,125],62⟩
  | 126 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | _ => default
theorem checked035 : ∀ y : BitVec 7, fastPotential 35 y = true →
    check 35 y (row035 y) = true := by decide

def row036 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked036 : ∀ y : BitVec 7, fastPotential 36 y = true →
    check 36 y (row036 y) = true := by decide

def row037 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked037 : ∀ y : BitVec 7, fastPotential 37 y = true →
    check 37 y (row037 y) = true := by decide

def row038 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked038 : ∀ y : BitVec 7, fastPotential 38 y = true →
    check 38 y (row038 y) = true := by decide

def row039 (y : BitVec 7) : Cut := match y.toNat with
  | 43 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 86 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 125 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,125],62⟩
  | _ => default
theorem checked039 : ∀ y : BitVec 7, fastPotential 39 y = true →
    check 39 y (row039 y) = true := by decide

def row040 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked040 : ∀ y : BitVec 7, fastPotential 40 y = true →
    check 40 y (row040 y) = true := by decide

def row041 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked041 : ∀ y : BitVec 7, fastPotential 41 y = true →
    check 41 y (row041 y) = true := by decide

def row042 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked042 : ∀ y : BitVec 7, fastPotential 42 y = true →
    check 42 y (row042 y) = true := by decide

def row043 (y : BitVec 7) : Cut := match y.toNat with
  | 12 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104],62⟩
  | 18 => ⟨[0,1,2,4,8,16,17,18,21,32,50,64,96,104],62⟩
  | 25 => ⟨[0,1,2,4,8,16,17,21,25,32,64,96,104],62⟩
  | 34 => ⟨[0,1,2,4,8,16,17,21,32,34,50,64,96,104],62⟩
  | 35 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 39 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 48 => ⟨[0,1,2,4,8,16,17,21,32,48,50,64,96,104],62⟩
  | 51 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 54 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 58 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 82 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 90 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 113 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | 114 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | _ => default
theorem checked043 : ∀ y : BitVec 7, fastPotential 43 y = true →
    check 43 y (row043 y) = true := by decide

def row044 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked044 : ∀ y : BitVec 7, fastPotential 44 y = true →
    check 44 y (row044 y) = true := by decide

def row045 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked045 : ∀ y : BitVec 7, fastPotential 45 y = true →
    check 45 y (row045 y) = true := by decide

def row046 (y : BitVec 7) : Cut := match y.toNat with
  | 35 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 82 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 113 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | _ => default
theorem checked046 : ∀ y : BitVec 7, fastPotential 46 y = true →
    check 46 y (row046 y) = true := by decide

def row047 (y : BitVec 7) : Cut := match y.toNat with
  | 35 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 82 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 113 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | _ => default
theorem checked047 : ∀ y : BitVec 7, fastPotential 47 y = true →
    check 47 y (row047 y) = true := by decide

def row048 (y : BitVec 7) : Cut := match y.toNat with
  | 43 => ⟨[0,1,2,4,8,16,17,21,32,48,50,64,96,104],62⟩
  | 86 => ⟨[0,1,2,4,8,16,17,21,32,48,50,64,96,104],62⟩
  | 125 => ⟨[0,1,2,4,8,16,17,21,32,48,50,64,96,104,125],62⟩
  | _ => default
theorem checked048 : ∀ y : BitVec 7, fastPotential 48 y = true →
    check 48 y (row048 y) = true := by decide

def row049 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked049 : ∀ y : BitVec 7, fastPotential 49 y = true →
    check 49 y (row049 y) = true := by decide

def row050 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked050 : ∀ y : BitVec 7, fastPotential 50 y = true →
    check 50 y (row050 y) = true := by decide

def row051 (y : BitVec 7) : Cut := match y.toNat with
  | 43 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 86 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 125 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,125],62⟩
  | _ => default
theorem checked051 : ∀ y : BitVec 7, fastPotential 51 y = true →
    check 51 y (row051 y) = true := by decide

def row052 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked052 : ∀ y : BitVec 7, fastPotential 52 y = true →
    check 52 y (row052 y) = true := by decide

def row053 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked053 : ∀ y : BitVec 7, fastPotential 53 y = true →
    check 53 y (row053 y) = true := by decide

def row054 (y : BitVec 7) : Cut := match y.toNat with
  | 3 => ⟨[0,1,2,3,4,8,16,17,21,32,64,67,96,104],62⟩
  | 35 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 43 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 65 => ⟨[0,1,2,4,8,16,17,21,32,64,65,67,96,104],62⟩
  | 66 => ⟨[0,1,2,4,8,16,17,21,32,64,66,67,96,104],62⟩
  | 71 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 75 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 82 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 83 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 86 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 99 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 113 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | 117 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,117],62⟩
  | 125 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,125],62⟩
  | _ => default
theorem checked054 : ∀ y : BitVec 7, fastPotential 54 y = true →
    check 54 y (row054 y) = true := by decide

def row055 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked055 : ∀ y : BitVec 7, fastPotential 55 y = true →
    check 55 y (row055 y) = true := by decide

def row056 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked056 : ∀ y : BitVec 7, fastPotential 56 y = true →
    check 56 y (row056 y) = true := by decide

def row057 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked057 : ∀ y : BitVec 7, fastPotential 57 y = true →
    check 57 y (row057 y) = true := by decide

def row058 (y : BitVec 7) : Cut := match y.toNat with
  | 3 => ⟨[0,1,2,3,4,8,16,17,21,32,64,67,96,104],62⟩
  | 35 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 43 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 65 => ⟨[0,1,2,4,8,16,17,21,32,64,65,67,96,104],62⟩
  | 66 => ⟨[0,1,2,4,8,16,17,21,32,64,66,67,96,104],62⟩
  | 71 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 75 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 82 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 83 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 86 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 99 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 113 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | 121 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,121],62⟩
  | 125 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,125],62⟩
  | _ => default
theorem checked058 : ∀ y : BitVec 7, fastPotential 58 y = true →
    check 58 y (row058 y) = true := by decide

def row059 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked059 : ∀ y : BitVec 7, fastPotential 59 y = true →
    check 59 y (row059 y) = true := by decide

def row060 (y : BitVec 7) : Cut := match y.toNat with
  | 35 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 82 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 113 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | _ => default
theorem checked060 : ∀ y : BitVec 7, fastPotential 60 y = true →
    check 60 y (row060 y) = true := by decide

def row061 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked061 : ∀ y : BitVec 7, fastPotential 61 y = true →
    check 61 y (row061 y) = true := by decide

def row062 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked062 : ∀ y : BitVec 7, fastPotential 62 y = true →
    check 62 y (row062 y) = true := by decide

def row063 (y : BitVec 7) : Cut := match y.toNat with
  | 35 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 82 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 113 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | _ => default
theorem checked063 : ∀ y : BitVec 7, fastPotential 63 y = true →
    check 63 y (row063 y) = true := by decide

def row064 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked064 : ∀ y : BitVec 7, fastPotential 64 y = true →
    check 64 y (row064 y) = true := by decide

def row065 (y : BitVec 7) : Cut := match y.toNat with
  | 12 => ⟨[0,1,2,4,8,12,16,17,21,32,64,65,67,96,104],62⟩
  | 54 => ⟨[0,1,2,4,8,16,17,21,32,64,65,67,96,104],62⟩
  | 58 => ⟨[0,1,2,4,8,16,17,21,32,64,65,67,96,104],62⟩
  | _ => default
theorem checked065 : ∀ y : BitVec 7, fastPotential 65 y = true →
    check 65 y (row065 y) = true := by decide

def row066 (y : BitVec 7) : Cut := match y.toNat with
  | 12 => ⟨[0,1,2,4,8,12,16,17,21,32,64,66,67,96,104],62⟩
  | 54 => ⟨[0,1,2,4,8,16,17,21,32,64,66,67,96,104],62⟩
  | 58 => ⟨[0,1,2,4,8,16,17,21,32,64,66,67,96,104],62⟩
  | _ => default
theorem checked066 : ∀ y : BitVec 7, fastPotential 66 y = true →
    check 66 y (row066 y) = true := by decide

def row067 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked067 : ∀ y : BitVec 7, fastPotential 67 y = true →
    check 67 y (row067 y) = true := by decide

def row068 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked068 : ∀ y : BitVec 7, fastPotential 68 y = true →
    check 68 y (row068 y) = true := by decide

def row069 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked069 : ∀ y : BitVec 7, fastPotential 69 y = true →
    check 69 y (row069 y) = true := by decide

def row070 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked070 : ∀ y : BitVec 7, fastPotential 70 y = true →
    check 70 y (row070 y) = true := by decide

def row071 (y : BitVec 7) : Cut := match y.toNat with
  | 12 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104],62⟩
  | 54 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 58 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | _ => default
theorem checked071 : ∀ y : BitVec 7, fastPotential 71 y = true →
    check 71 y (row071 y) = true := by decide

def row072 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked072 : ∀ y : BitVec 7, fastPotential 72 y = true →
    check 72 y (row072 y) = true := by decide

def row073 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked073 : ∀ y : BitVec 7, fastPotential 73 y = true →
    check 73 y (row073 y) = true := by decide

def row074 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked074 : ∀ y : BitVec 7, fastPotential 74 y = true →
    check 74 y (row074 y) = true := by decide

def row075 (y : BitVec 7) : Cut := match y.toNat with
  | 12 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104],62⟩
  | 54 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 58 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | _ => default
theorem checked075 : ∀ y : BitVec 7, fastPotential 75 y = true →
    check 75 y (row075 y) = true := by decide

def row076 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked076 : ∀ y : BitVec 7, fastPotential 76 y = true →
    check 76 y (row076 y) = true := by decide

def row077 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked077 : ∀ y : BitVec 7, fastPotential 77 y = true →
    check 77 y (row077 y) = true := by decide

def row078 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked078 : ∀ y : BitVec 7, fastPotential 78 y = true →
    check 78 y (row078 y) = true := by decide

def row079 (y : BitVec 7) : Cut := match y.toNat with
  | 12 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104],62⟩
  | 113 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | 125 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,125],62⟩
  | _ => default
theorem checked079 : ∀ y : BitVec 7, fastPotential 79 y = true →
    check 79 y (row079 y) = true := by decide

def row080 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked080 : ∀ y : BitVec 7, fastPotential 80 y = true →
    check 80 y (row080 y) = true := by decide

def row081 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked081 : ∀ y : BitVec 7, fastPotential 81 y = true →
    check 81 y (row081 y) = true := by decide

def row082 (y : BitVec 7) : Cut := match y.toNat with
  | 12 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104],62⟩
  | 30 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 43 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 46 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 47 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 54 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 58 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 60 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 63 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 86 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 94 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 108 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,108],62⟩
  | 125 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,125],62⟩
  | 126 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | _ => default
theorem checked082 : ∀ y : BitVec 7, fastPotential 82 y = true →
    check 82 y (row082 y) = true := by decide

def row083 (y : BitVec 7) : Cut := match y.toNat with
  | 12 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104],62⟩
  | 54 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 58 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | _ => default
theorem checked083 : ∀ y : BitVec 7, fastPotential 83 y = true →
    check 83 y (row083 y) = true := by decide

def row084 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked084 : ∀ y : BitVec 7, fastPotential 84 y = true →
    check 84 y (row084 y) = true := by decide

def row085 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked085 : ∀ y : BitVec 7, fastPotential 85 y = true →
    check 85 y (row085 y) = true := by decide

def row086 (y : BitVec 7) : Cut := match y.toNat with
  | 12 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104],62⟩
  | 18 => ⟨[0,1,2,4,8,16,17,18,21,32,50,64,96,104],62⟩
  | 34 => ⟨[0,1,2,4,8,16,17,21,32,34,50,64,96,104],62⟩
  | 35 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 39 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 48 => ⟨[0,1,2,4,8,16,17,21,32,48,50,64,96,104],62⟩
  | 51 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 54 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 58 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 82 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 90 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 100 => ⟨[0,1,2,4,8,16,17,21,32,64,96,100,104],62⟩
  | 113 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | 114 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | _ => default
theorem checked086 : ∀ y : BitVec 7, fastPotential 86 y = true →
    check 86 y (row086 y) = true := by decide

def row087 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked087 : ∀ y : BitVec 7, fastPotential 87 y = true →
    check 87 y (row087 y) = true := by decide

def row088 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked088 : ∀ y : BitVec 7, fastPotential 88 y = true →
    check 88 y (row088 y) = true := by decide

def row089 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked089 : ∀ y : BitVec 7, fastPotential 89 y = true →
    check 89 y (row089 y) = true := by decide

def row090 (y : BitVec 7) : Cut := match y.toNat with
  | 43 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 86 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 125 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,125],62⟩
  | _ => default
theorem checked090 : ∀ y : BitVec 7, fastPotential 90 y = true →
    check 90 y (row090 y) = true := by decide

def row091 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked091 : ∀ y : BitVec 7, fastPotential 91 y = true →
    check 91 y (row091 y) = true := by decide

def row092 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked092 : ∀ y : BitVec 7, fastPotential 92 y = true →
    check 92 y (row092 y) = true := by decide

def row093 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked093 : ∀ y : BitVec 7, fastPotential 93 y = true →
    check 93 y (row093 y) = true := by decide

def row094 (y : BitVec 7) : Cut := match y.toNat with
  | 35 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 82 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 113 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | _ => default
theorem checked094 : ∀ y : BitVec 7, fastPotential 94 y = true →
    check 94 y (row094 y) = true := by decide

def row095 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked095 : ∀ y : BitVec 7, fastPotential 95 y = true →
    check 95 y (row095 y) = true := by decide

def row096 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked096 : ∀ y : BitVec 7, fastPotential 96 y = true →
    check 96 y (row096 y) = true := by decide

def row097 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked097 : ∀ y : BitVec 7, fastPotential 97 y = true →
    check 97 y (row097 y) = true := by decide

def row098 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked098 : ∀ y : BitVec 7, fastPotential 98 y = true →
    check 98 y (row098 y) = true := by decide

def row099 (y : BitVec 7) : Cut := match y.toNat with
  | 12 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104],62⟩
  | 54 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 58 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | _ => default
theorem checked099 : ∀ y : BitVec 7, fastPotential 99 y = true →
    check 99 y (row099 y) = true := by decide

def row100 (y : BitVec 7) : Cut := match y.toNat with
  | 86 => ⟨[0,1,2,4,8,16,17,21,32,64,96,100,104],62⟩
  | _ => default
theorem checked100 : ∀ y : BitVec 7, fastPotential 100 y = true →
    check 100 y (row100 y) = true := by decide

def row101 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked101 : ∀ y : BitVec 7, fastPotential 101 y = true →
    check 101 y (row101 y) = true := by decide

def row102 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked102 : ∀ y : BitVec 7, fastPotential 102 y = true →
    check 102 y (row102 y) = true := by decide

def row103 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked103 : ∀ y : BitVec 7, fastPotential 103 y = true →
    check 103 y (row103 y) = true := by decide

def row104 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked104 : ∀ y : BitVec 7, fastPotential 104 y = true →
    check 104 y (row104 y) = true := by decide

def row105 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked105 : ∀ y : BitVec 7, fastPotential 105 y = true →
    check 105 y (row105 y) = true := by decide

def row106 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked106 : ∀ y : BitVec 7, fastPotential 106 y = true →
    check 106 y (row106 y) = true := by decide

def row107 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked107 : ∀ y : BitVec 7, fastPotential 107 y = true →
    check 107 y (row107 y) = true := by decide

def row108 (y : BitVec 7) : Cut := match y.toNat with
  | 82 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,108],62⟩
  | _ => default
theorem checked108 : ∀ y : BitVec 7, fastPotential 108 y = true →
    check 108 y (row108 y) = true := by decide

def row109 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked109 : ∀ y : BitVec 7, fastPotential 109 y = true →
    check 109 y (row109 y) = true := by decide

def row110 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked110 : ∀ y : BitVec 7, fastPotential 110 y = true →
    check 110 y (row110 y) = true := by decide

def row111 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked111 : ∀ y : BitVec 7, fastPotential 111 y = true →
    check 111 y (row111 y) = true := by decide

def row112 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked112 : ∀ y : BitVec 7, fastPotential 112 y = true →
    check 112 y (row112 y) = true := by decide

def row113 (y : BitVec 7) : Cut := match y.toNat with
  | 12 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104,113],62⟩
  | 30 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | 43 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | 46 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | 47 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | 54 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | 58 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | 60 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | 63 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | 79 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | 86 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | 94 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | 125 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113,125],62⟩
  | 126 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | _ => default
theorem checked113 : ∀ y : BitVec 7, fastPotential 113 y = true →
    check 113 y (row113 y) = true := by decide

def row114 (y : BitVec 7) : Cut := match y.toNat with
  | 43 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 86 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 125 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,125],62⟩
  | _ => default
theorem checked114 : ∀ y : BitVec 7, fastPotential 114 y = true →
    check 114 y (row114 y) = true := by decide

def row115 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked115 : ∀ y : BitVec 7, fastPotential 115 y = true →
    check 115 y (row115 y) = true := by decide

def row116 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked116 : ∀ y : BitVec 7, fastPotential 116 y = true →
    check 116 y (row116 y) = true := by decide

def row117 (y : BitVec 7) : Cut := match y.toNat with
  | 54 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,117],62⟩
  | _ => default
theorem checked117 : ∀ y : BitVec 7, fastPotential 117 y = true →
    check 117 y (row117 y) = true := by decide

def row118 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked118 : ∀ y : BitVec 7, fastPotential 118 y = true →
    check 118 y (row118 y) = true := by decide

def row119 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked119 : ∀ y : BitVec 7, fastPotential 119 y = true →
    check 119 y (row119 y) = true := by decide

def row120 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked120 : ∀ y : BitVec 7, fastPotential 120 y = true →
    check 120 y (row120 y) = true := by decide

def row121 (y : BitVec 7) : Cut := match y.toNat with
  | 58 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,121],62⟩
  | _ => default
theorem checked121 : ∀ y : BitVec 7, fastPotential 121 y = true →
    check 121 y (row121 y) = true := by decide

def row122 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked122 : ∀ y : BitVec 7, fastPotential 122 y = true →
    check 122 y (row122 y) = true := by decide

def row123 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked123 : ∀ y : BitVec 7, fastPotential 123 y = true →
    check 123 y (row123 y) = true := by decide

def row124 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked124 : ∀ y : BitVec 7, fastPotential 124 y = true →
    check 124 y (row124 y) = true := by decide

def row125 (y : BitVec 7) : Cut := match y.toNat with
  | 12 => ⟨[0,1,2,4,8,12,16,17,21,32,64,96,104,125],62⟩
  | 18 => ⟨[0,1,2,4,8,16,17,18,21,32,50,64,96,104,125],62⟩
  | 34 => ⟨[0,1,2,4,8,16,17,21,32,34,50,64,96,104,125],62⟩
  | 35 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,125],62⟩
  | 39 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,125],62⟩
  | 48 => ⟨[0,1,2,4,8,16,17,21,32,48,50,64,96,104,125],62⟩
  | 51 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,125],62⟩
  | 54 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,125],62⟩
  | 58 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,125],62⟩
  | 79 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,125],62⟩
  | 82 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,125],62⟩
  | 90 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,125],62⟩
  | 113 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113,125],62⟩
  | 114 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,125],62⟩
  | _ => default
theorem checked125 : ∀ y : BitVec 7, fastPotential 125 y = true →
    check 125 y (row125 y) = true := by decide

def row126 (y : BitVec 7) : Cut := match y.toNat with
  | 35 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 82 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104],62⟩
  | 113 => ⟨[0,1,2,4,8,16,17,21,32,64,96,104,113],62⟩
  | _ => default
theorem checked126 : ∀ y : BitVec 7, fastPotential 126 y = true →
    check 126 y (row126 y) = true := by decide

def row127 (y : BitVec 7) : Cut := match y.toNat with
  | _ => default
theorem checked127 : ∀ y : BitVec 7, fastPotential 127 y = true →
    check 127 y (row127 y) = true := by decide

def certificate (x y : BitVec 7) : Cut := match x.toNat with
  | 0 => row000 y
  | 1 => row001 y
  | 2 => row002 y
  | 3 => row003 y
  | 4 => row004 y
  | 5 => row005 y
  | 6 => row006 y
  | 7 => row007 y
  | 8 => row008 y
  | 9 => row009 y
  | 10 => row010 y
  | 11 => row011 y
  | 12 => row012 y
  | 13 => row013 y
  | 14 => row014 y
  | 15 => row015 y
  | 16 => row016 y
  | 17 => row017 y
  | 18 => row018 y
  | 19 => row019 y
  | 20 => row020 y
  | 21 => row021 y
  | 22 => row022 y
  | 23 => row023 y
  | 24 => row024 y
  | 25 => row025 y
  | 26 => row026 y
  | 27 => row027 y
  | 28 => row028 y
  | 29 => row029 y
  | 30 => row030 y
  | 31 => row031 y
  | 32 => row032 y
  | 33 => row033 y
  | 34 => row034 y
  | 35 => row035 y
  | 36 => row036 y
  | 37 => row037 y
  | 38 => row038 y
  | 39 => row039 y
  | 40 => row040 y
  | 41 => row041 y
  | 42 => row042 y
  | 43 => row043 y
  | 44 => row044 y
  | 45 => row045 y
  | 46 => row046 y
  | 47 => row047 y
  | 48 => row048 y
  | 49 => row049 y
  | 50 => row050 y
  | 51 => row051 y
  | 52 => row052 y
  | 53 => row053 y
  | 54 => row054 y
  | 55 => row055 y
  | 56 => row056 y
  | 57 => row057 y
  | 58 => row058 y
  | 59 => row059 y
  | 60 => row060 y
  | 61 => row061 y
  | 62 => row062 y
  | 63 => row063 y
  | 64 => row064 y
  | 65 => row065 y
  | 66 => row066 y
  | 67 => row067 y
  | 68 => row068 y
  | 69 => row069 y
  | 70 => row070 y
  | 71 => row071 y
  | 72 => row072 y
  | 73 => row073 y
  | 74 => row074 y
  | 75 => row075 y
  | 76 => row076 y
  | 77 => row077 y
  | 78 => row078 y
  | 79 => row079 y
  | 80 => row080 y
  | 81 => row081 y
  | 82 => row082 y
  | 83 => row083 y
  | 84 => row084 y
  | 85 => row085 y
  | 86 => row086 y
  | 87 => row087 y
  | 88 => row088 y
  | 89 => row089 y
  | 90 => row090 y
  | 91 => row091 y
  | 92 => row092 y
  | 93 => row093 y
  | 94 => row094 y
  | 95 => row095 y
  | 96 => row096 y
  | 97 => row097 y
  | 98 => row098 y
  | 99 => row099 y
  | 100 => row100 y
  | 101 => row101 y
  | 102 => row102 y
  | 103 => row103 y
  | 104 => row104 y
  | 105 => row105 y
  | 106 => row106 y
  | 107 => row107 y
  | 108 => row108 y
  | 109 => row109 y
  | 110 => row110 y
  | 111 => row111 y
  | 112 => row112 y
  | 113 => row113 y
  | 114 => row114 y
  | 115 => row115 y
  | 116 => row116 y
  | 117 => row117 y
  | 118 => row118 y
  | 119 => row119 y
  | 120 => row120 y
  | 121 => row121 y
  | 122 => row122 y
  | 123 => row123 y
  | 124 => row124 y
  | 125 => row125 y
  | 126 => row126 y
  | 127 => row127 y
  | _ => default

theorem word_cases : ∀ x : BitVec 7,
    x ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127] := by decide

theorem all_checked (x y : BitVec 7) (h : fastPotential x y = true) :
    check x y (certificate x y) = true := by
  have hx := word_cases x
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked000 y h
  · exact checked001 y h
  · exact checked002 y h
  · exact checked003 y h
  · exact checked004 y h
  · exact checked005 y h
  · exact checked006 y h
  · exact checked007 y h
  · exact checked008 y h
  · exact checked009 y h
  · exact checked010 y h
  · exact checked011 y h
  · exact checked012 y h
  · exact checked013 y h
  · exact checked014 y h
  · exact checked015 y h
  · exact checked016 y h
  · exact checked017 y h
  · exact checked018 y h
  · exact checked019 y h
  · exact checked020 y h
  · exact checked021 y h
  · exact checked022 y h
  · exact checked023 y h
  · exact checked024 y h
  · exact checked025 y h
  · exact checked026 y h
  · exact checked027 y h
  · exact checked028 y h
  · exact checked029 y h
  · exact checked030 y h
  · exact checked031 y h
  · exact checked032 y h
  · exact checked033 y h
  · exact checked034 y h
  · exact checked035 y h
  · exact checked036 y h
  · exact checked037 y h
  · exact checked038 y h
  · exact checked039 y h
  · exact checked040 y h
  · exact checked041 y h
  · exact checked042 y h
  · exact checked043 y h
  · exact checked044 y h
  · exact checked045 y h
  · exact checked046 y h
  · exact checked047 y h
  · exact checked048 y h
  · exact checked049 y h
  · exact checked050 y h
  · exact checked051 y h
  · exact checked052 y h
  · exact checked053 y h
  · exact checked054 y h
  · exact checked055 y h
  · exact checked056 y h
  · exact checked057 y h
  · exact checked058 y h
  · exact checked059 y h
  · exact checked060 y h
  · exact checked061 y h
  · exact checked062 y h
  · exact checked063 y h
  · exact checked064 y h
  · exact checked065 y h
  · exact checked066 y h
  · exact checked067 y h
  · exact checked068 y h
  · exact checked069 y h
  · exact checked070 y h
  · exact checked071 y h
  · exact checked072 y h
  · exact checked073 y h
  · exact checked074 y h
  · exact checked075 y h
  · exact checked076 y h
  · exact checked077 y h
  · exact checked078 y h
  · exact checked079 y h
  · exact checked080 y h
  · exact checked081 y h
  · exact checked082 y h
  · exact checked083 y h
  · exact checked084 y h
  · exact checked085 y h
  · exact checked086 y h
  · exact checked087 y h
  · exact checked088 y h
  · exact checked089 y h
  · exact checked090 y h
  · exact checked091 y h
  · exact checked092 y h
  · exact checked093 y h
  · exact checked094 y h
  · exact checked095 y h
  · exact checked096 y h
  · exact checked097 y h
  · exact checked098 y h
  · exact checked099 y h
  · exact checked100 y h
  · exact checked101 y h
  · exact checked102 y h
  · exact checked103 y h
  · exact checked104 y h
  · exact checked105 y h
  · exact checked106 y h
  · exact checked107 y h
  · exact checked108 y h
  · exact checked109 y h
  · exact checked110 y h
  · exact checked111 y h
  · exact checked112 y h
  · exact checked113 y h
  · exact checked114 y h
  · exact checked115 y h
  · exact checked116 y h
  · exact checked117 y h
  · exact checked118 y h
  · exact checked119 y h
  · exact checked120 y h
  · exact checked121 y h
  · exact checked122 y h
  · exact checked123 y h
  · exact checked124 y h
  · exact checked125 y h
  · exact checked126 y h
  · exact checked127 y h

theorem two_extras_impossible (p : List (BitVec 7)) (x y : BitVec 7)
    (hv : FreeXor.validMasks initial p = true) (bounded : p ⊆ allowed x y)
    (reaches : goals ⊆ initial ++ p) : False := by
  have hp := potential_required p x y hv bounded reaches
  rw [fastPotential_correct] at hp
  exact checked_cut_excludes x y (certificate x y) (all_checked x y hp)
    p hv bounded reaches

end HGP13.TransposeCertificate
