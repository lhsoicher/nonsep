# The nonsep repository: non-separating primitive groups

This repository contains the main GAP program for determining the
non-separating primitive groups of given degrees, and of these,
the non-synchronizing ones. Also here is a log-file of a run of
this program for degrees 2,3,...,624, giving the non-separating
groups found together with some basic information. Also included is a
GAP-readable file nonsep_records.g produced by the program run, containing
detailed information on the non-separating groups classified. The file
nonsep_records.g consists of a list `nonsep_records`, and for 1<n<=624,
its n-th element is a list (possibly empty) of information records for
the non-separating primitive groups of degree n. You should load the
FinInG package before reading nonsep_records.g into GAP.

This repository is Copyright 2024 Leonard Soicher, all rights reserved.
