# Manual transcription audit for the table `[[14,3,4]]` fixture

Source retrieved 2026-07-24:
<https://codetables.de/QECC.php?k=3&n=14&q=4>

The page labels the displayed matrix `stabilizer matrix`, with each row shown
as 14 left entries, a vertical separator, and 14 right entries. The project
specification and table convention read these halves as `[X|Z]`. Each coordinate
was manually mapped by `(x,z): 00 -> I, 10 -> X, 01 -> Z, 11 -> Y`.

| row | source X half | source Z half | Pauli fixture row |
| ---: | --- | --- | --- |
| 1 | `10001001001000` | `00001000111100` | `XIIIYIIXZZYZII` |
| 2 | `00001100101000` | `10010101101100` | `ZIIZXYIZYIYZII` |
| 3 | `01000101000100` | `00001000000000` | `IXIIZXIXIIIXII` |
| 4 | `00001100010100` | `01011001011100` | `IZIZYXIZIYZYII` |
| 5 | `00101100111100` | `00000100011000` | `IIXIXYIIXYYXII` |
| 6 | `00000000001100` | `00111100111100` | `IIZZZZIIZZYYII` |
| 7 | `00010000001100` | `00000100010100` | `IIIXIZIIIZXYII` |
| 8 | `00000011111100` | `00000000000000` | `IIIIIIXXXXXXII` |
| 9 | `00000000000000` | `00000011111100` | `IIIIIIZZZZZZII` |
| 10 | `00000000000010` | `00000000000000` | `IIIIIIIIIIIIXI` |
| 11 | `00000000000001` | `00000000000000` | `IIIIIIIIIIIIIX` |

Checks independent of the source's claimed parameters:

- the 11 Pauli rows commute pairwise;
- their `2^11 = 2048` subset products are all distinct;
- hence the binary stabilizer rank is 11 and `k=14-11=3`;
- bounded Pauli enumeration finds no logical below weight four and finds 105
  logical Pauli strings at weight four;
- therefore the transcribed fixture has exact parameters `[[14,3,4]]`.

The page says this construction was last modified 2005-06-30; the page footer
reports a table-wide last change of 2024-06-10.
