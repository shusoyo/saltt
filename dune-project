(lang dune 3.21)

(name saltt)

(generate_opam_files true)

(source
 (github shusoyo/saltt))

(authors "shusoyo")

(maintainers "shusoyo")

(license LICENSE)

(pin
 (url "git+https://github.com/shusoyo/oscar.git")
 (package
  (name oscar)))

(package
 (name saltt)
 (synopsis "A salt flavored type theory")
 (description "saltt is a salt flavored type theory in OCaml.")
 (depends
  (ocaml
   (>= 5.0.0))
  (dune
   (>= 3.21))
  oscar)
 (tags
  ("type-theory" "ocaml")))
