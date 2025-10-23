Main changes from nonsep 0.2 to nonsep 0.3 (October 2025)
---------------------------------------------------------

1. Fixed bug in new_nonsynch_5.g, where the independence number
was given as the clique number for certain non-synchronizing graphs with
vertex_degree >= (graph_order-1)/2.  However, this error only affected
the comment component for relevant elements of nonsep_records in the
file nonsep_records.g and the printed such comments in the log-file
new_nonsynch_5.log. The bug did **not** affect the Journal of Algebra
paper "The non-synchronizing primitive groups of degree up to 624".
The clique numbers given in that paper are all believed to be correct.

2. Re-ran new_nonsynch_5.g using GAP 4.15.0 and its included packages to
produce new corrected files nonsep_records.g and new_nonsynch_5.log. Some
specific graph data presented in these files has changed.

3. Updated the file README.md. 

4. Added the file CHANGES.md.

