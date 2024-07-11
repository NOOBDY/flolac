module test where

? : ~~a -> (a->~~b) -> ~~b
λ(x:¬¬a)(y:a→¬¬b)(z:¬b). ?:⊥
λ(x:¬¬a)(y:a→¬¬b)(z:¬b). x ?:¬a
λ(x:¬¬a)(y:a→¬¬b)(z:¬b). x (λ(w:a).?:⊥)
λ(x:¬¬a)(y:a→¬¬b)(z:¬b). x (λ(w:a).y w z)
λxyz.x(λw.ywz)
