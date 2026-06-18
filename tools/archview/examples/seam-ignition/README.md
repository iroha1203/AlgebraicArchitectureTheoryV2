# H1 Gluing Obstruction Frame Comparison

ArchView can replay a sequence of emitted ArchSig packets. Each frame is an
independent `archsig analyze` run; ArchView compares adjacent emitted
conclusions and does not create a new verdict.

## Frames

| frame | ArchMap | emitted conclusion | note |
| --- | --- | --- | --- |
| f0 | `frame-00.archmap.json` | `NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` | raw section values agree |
| f1 | `frame-01.archmap.json` | `MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` | left and bottom raw section values differ |
| f2 | `frame-02.archmap.json` | `NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` | raw section values agree again |

The sequence view keeps camera placement stable across frames and labels only
adjacent emitted-conclusion changes.

## Run

```bash
tools/archview/examples/seam-ignition/build-sequence.sh
python3 -m http.server 8000 --directory .tmp/archview-seq
```

Open `http://localhost:8000/archview.html`.
