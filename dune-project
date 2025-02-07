(lang dune 3.13)
(using menhir 3.0)

(name stml)

(generate_opam_files true)

(authors "Mickael Laurent")

(maintainers "Mickael Laurent")

(homepage "https://github.com/E-Sh4rk/stml")

(bug_reports "https://github.com/E-Sh4rk/stml/issues")

(license "MIT")

(package
 (name stml)
 (synopsis "A prototype type-checker for dynamic languages")
 (depends (ocaml (>= 5.3.0)) dune (sstt (>= 0.1.0)) ppx_deriving zarith pomap tsort yojson js_of_ocaml-ppx zarith_stubs_js)
)
