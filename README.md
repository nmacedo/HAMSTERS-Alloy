# HAMSTERS in Alloy

The repository contains the formalization in [Alloy](http://alloytools.org) of task models in the [HAMSTERS](https://www.irit.fr/recherches/ICS/softwares/hamsters/) notation. It also contains the formalization of a concrete task model for an [Arrival MANager (AMAN)](https://sites.google.com/view/abz-aman-casestudy/home) interactive system. These models accompany the paper "*Task Model Design and Analysis with Alloy*", currently under revision.

It contains the following files:
- `HAMSTERS.als`, the formalization of the structural and behavioral semantics of HAMSTERS
- `AMAN.als`, the specification of the AMAN task model and the composed interactive system
- `AMAN_fixed.als`, a fixed version of AMAN to guarantee feedback and availability
- `AMAN.thm`, an Alloy custom theme to better visualize traces from the AMAN model

