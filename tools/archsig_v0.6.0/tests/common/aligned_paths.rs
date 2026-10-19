use archsig::{definition::check_definitions, observed::input::InputSources};
pub const DEFINITIONS: &str = r#"{
  "format": "archsig.atom-definition/1",
  "semantics": "archsig/0.6.0",
  "vocabularies": [
    {
      "namespace": "Flow",
      "version": "1",
      "semantics": "archsig/0.6.0",
      "dependencies": [],
      "declarations": [
        {
          "kind": "entity",
          "name": "Flow.Left",
          "meaning": "Left",
          "parameters": [],
          "fields": [],
          "alignments": []
        },
        {
          "kind": "entity",
          "name": "Flow.Right",
          "meaning": "Right",
          "parameters": [],
          "fields": [],
          "alignments": []
        },
        {
          "kind": "entity",
          "name": "Flow.External",
          "meaning": "External",
          "parameters": [],
          "fields": [
            {
              "name": "qty",
              "type": "Z",
              "meaning": "qty"
            }
          ],
          "alignments": []
        },
        {
          "kind": "entity",
          "name": "Flow.LNode",
          "meaning": "LNode",
          "parameters": [
            {
              "name": "owner",
              "type": [
                "Ref",
                "Flow.Left"
              ],
              "meaning": "owner"
            }
          ],
          "fields": [
            {
              "name": "qty",
              "type": "Z",
              "meaning": "qty"
            },
            {
              "name": "refs",
              "type": [
                "Tuple",
                [
                  "List",
                  [
                    "Ref",
                    "Flow.LNode"
                  ]
                ],
                [
                  "Option",
                  [
                    "Ref",
                    "Flow.LNode"
                  ]
                ],
                [
                  "Set",
                  [
                    "Ref",
                    "Flow.LNode"
                  ]
                ]
              ],
              "meaning": "refs"
            },
            {
              "name": "external",
              "type": [
                "Ref",
                "Flow.External"
              ],
              "meaning": "external"
            }
          ],
          "alignments": []
        },
        {
          "kind": "entity",
          "name": "Flow.RNode",
          "meaning": "RNode",
          "parameters": [
            {
              "name": "owner",
              "type": [
                "Ref",
                "Flow.Right"
              ],
              "meaning": "owner"
            }
          ],
          "fields": [
            {
              "name": "amount",
              "type": "Q",
              "meaning": "amount"
            },
            {
              "name": "targets",
              "type": [
                "Tuple",
                [
                  "List",
                  [
                    "Ref",
                    "Flow.RNode"
                  ]
                ],
                [
                  "Option",
                  [
                    "Ref",
                    "Flow.RNode"
                  ]
                ],
                [
                  "Set",
                  [
                    "Ref",
                    "Flow.RNode"
                  ]
                ]
              ],
              "meaning": "targets"
            },
            {
              "name": "outside",
              "type": [
                "Ref",
                "Flow.External"
              ],
              "meaning": "outside"
            }
          ],
          "alignments": []
        },
        {
          "kind": "correspondence",
          "name": "Flow.Move",
          "meaning": "move",
          "parameters": [
            {
              "name": "from",
              "type": [
                "Ref",
                "Flow.Left"
              ],
              "meaning": "from"
            },
            {
              "name": "to",
              "type": [
                "Ref",
                "Flow.Right"
              ],
              "meaning": "to"
            }
          ],
          "fields": [
            {
              "name": "nodes",
              "type": [
                "Map",
                [
                  "Owned",
                  "Flow.LNode",
                  "from"
                ],
                [
                  "Owned",
                  "Flow.RNode",
                  "to"
                ]
              ],
              "meaning": "nodes"
            }
          ],
          "alignments": [
            {
              "source": "Flow.LNode.owner",
              "target": "Flow.RNode.owner",
              "meaning": "owner"
            },
            {
              "source": "Flow.LNode.qty",
              "target": "Flow.RNode.amount",
              "meaning": "qty"
            },
            {
              "source": "Flow.LNode.refs",
              "target": "Flow.RNode.targets",
              "meaning": "refs"
            },
            {
              "source": "Flow.LNode.external",
              "target": "Flow.RNode.outside",
              "meaning": "external"
            }
          ]
        }
      ]
    }
  ]
}"#;
pub const MAP: &str = r#"{
  "format": "archsig.archmap/2",
  "semantics": "archsig/0.6.0",
  "vocabularies": [
    {
      "namespace": "Flow",
      "version": "1",
      "digest": "DIGEST"
    }
  ],
  "sources": [],
  "origins": [
    {
      "id": "o",
      "mode": "specification",
      "method": "small aligned references",
      "note": "small reference fixture",
      "locations": []
    }
  ],
  "snapshots": [
    {
      "id": "v",
      "origin": "o",
      "subjects": [
        {
          "id": "A",
          "type": "Flow.Left",
          "origin": "o"
        },
        {
          "id": "B",
          "type": "Flow.Right",
          "origin": "o"
        },
        {
          "id": "z",
          "type": "Flow.External",
          "origin": "o"
        },
        {
          "id": "p",
          "type": "Flow.LNode",
          "origin": "o"
        },
        {
          "id": "q",
          "type": "Flow.LNode",
          "origin": "o"
        },
        {
          "id": "r",
          "type": "Flow.RNode",
          "origin": "o"
        },
        {
          "id": "m",
          "type": "Flow.Move",
          "origin": "o"
        }
      ],
      "atoms": [
        {
          "id": "p-owner",
          "subject": "p",
          "field": "Flow.LNode.owner",
          "value": [
            "v",
            "A"
          ],
          "origin": "o"
        },
        {
          "id": "p-qty",
          "subject": "p",
          "field": "Flow.LNode.qty",
          "value": "2",
          "origin": "o"
        },
        {
          "id": "p-refs",
          "subject": "p",
          "field": "Flow.LNode.refs",
          "value": [
            [
              [
                "v",
                "p"
              ],
              [
                "v",
                "q"
              ],
              [
                "v",
                "p"
              ]
            ],
            {
              "some": [
                "v",
                "q"
              ]
            },
            [
              [
                "v",
                "p"
              ],
              [
                "v",
                "q"
              ]
            ]
          ],
          "origin": "o"
        },
        {
          "id": "p-external",
          "subject": "p",
          "field": "Flow.LNode.external",
          "value": [
            "v",
            "z"
          ],
          "origin": "o"
        },
        {
          "id": "q-owner",
          "subject": "q",
          "field": "Flow.LNode.owner",
          "value": [
            "v",
            "A"
          ],
          "origin": "o"
        },
        {
          "id": "q-qty",
          "subject": "q",
          "field": "Flow.LNode.qty",
          "value": "9",
          "origin": "o"
        },
        {
          "id": "q-refs",
          "subject": "q",
          "field": "Flow.LNode.refs",
          "value": [
            [
              [
                "v",
                "q"
              ],
              [
                "v",
                "q"
              ],
              [
                "v",
                "q"
              ]
            ],
            {
              "some": [
                "v",
                "q"
              ]
            },
            [
              [
                "v",
                "q"
              ]
            ]
          ],
          "origin": "o"
        },
        {
          "id": "q-external",
          "subject": "q",
          "field": "Flow.LNode.external",
          "value": [
            "v",
            "z"
          ],
          "origin": "o"
        },
        {
          "id": "r-owner",
          "subject": "r",
          "field": "Flow.RNode.owner",
          "value": [
            "v",
            "B"
          ],
          "origin": "o"
        },
        {
          "id": "r-amount",
          "subject": "r",
          "field": "Flow.RNode.amount",
          "value": ["7", "2"],
          "origin": "o"
        },
        {
          "id": "r-targets",
          "subject": "r",
          "field": "Flow.RNode.targets",
          "value": [
            [
              [
                "v",
                "r"
              ],
              [
                "v",
                "r"
              ],
              [
                "v",
                "r"
              ]
            ],
            {
              "some": [
                "v",
                "r"
              ]
            },
            [
              [
                "v",
                "r"
              ]
            ]
          ],
          "origin": "o"
        },
        {
          "id": "r-outside",
          "subject": "r",
          "field": "Flow.RNode.outside",
          "value": [
            "v",
            "z"
          ],
          "origin": "o"
        },
        {
          "id": "z-qty",
          "subject": "z",
          "field": "Flow.External.qty",
          "value": "17",
          "origin": "o"
        },
        {
          "id": "m-from",
          "subject": "m",
          "field": "Flow.Move.from",
          "value": [
            "v",
            "A"
          ],
          "origin": "o"
        },
        {
          "id": "m-to",
          "subject": "m",
          "field": "Flow.Move.to",
          "value": [
            "v",
            "B"
          ],
          "origin": "o"
        },
        {
          "id": "m-nodes",
          "subject": "m",
          "field": "Flow.Move.nodes",
          "value": [
            [
              [
                "v",
                "p"
              ],
              [
                "v",
                "r"
              ]
            ],
            [
              [
                "v",
                "q"
              ],
              [
                "v",
                "r"
              ]
            ]
          ],
          "origin": "o"
        }
      ]
    }
  ]
}"#;
pub fn input(quantity_variant: bool) -> InputSources {
    let d = check_definitions(&[("definition0", DEFINITIONS.as_bytes())]).unwrap();
    let digest = &d.vocabularies["Flow"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Flow {{use vocabulary Flow version \"1\" digest \"{digest}\";view step(m:Move):Path<Left,Right> =path(m);view maybe(m:Move):Option<Path<Left,Right>> =some(path(m));view left(m:Move):Bool=then(identity(source(path(m))),path(m))=path(m);view right(m:Move):Bool=then(path(m),identity(target(path(m))))=path(m);}}"
    );
    let map = MAP.replace("DIGEST", digest);
    let map = if quantity_variant {
        map.replacen("\"7\"", "\"99\"", 1)
    } else {
        map
    };
    InputSources::from_bytes(
        vec![DEFINITIONS.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
pub fn mismatched_input(kind: usize) -> InputSources {
    let normal = input(false);
    let mut map = super::fixture::convert(&archsig::json::parse(normal.archmap().bytes()).unwrap());
    let archsig::canonical::Json::Obj(root) = &mut map else {
        panic!()
    };
    let archsig::canonical::Json::Arr(snaps) = root.get_mut("snapshots").unwrap() else {
        panic!()
    };
    let archsig::canonical::Json::Obj(snap) = &mut snaps[0] else {
        panic!()
    };
    let archsig::canonical::Json::Arr(atoms) = snap.get_mut("atoms").unwrap() else {
        panic!()
    };
    for a in atoms {
        let archsig::canonical::Json::Obj(a) = a else {
            panic!()
        };
        if a["id"] == archsig::canonical::Json::str("r-targets") {
            let archsig::canonical::Json::Arr(parts) = a.get_mut("value").unwrap() else {
                panic!()
            };
            match kind {
                0 => {
                    let archsig::canonical::Json::Arr(list) = &mut parts[0] else {
                        panic!()
                    };
                    list.pop();
                }
                1 => {
                    parts[1] = archsig::canonical::Json::obj([(
                        "none",
                        archsig::canonical::Json::Bool(true),
                    )])
                }
                _ => parts[2] = archsig::canonical::Json::Arr(vec![]),
            }
        }
    }
    InputSources::from_bytes(
        vec![DEFINITIONS.as_bytes().to_vec()],
        normal.law().bytes().to_vec(),
        map.canonical().into_bytes(),
    )
}
pub fn unmatched_root_field_input() -> InputSources {
    use archsig::{canonical::Json, json::parse};
    let normal = input(false);
    let mut definitions = super::fixture::convert(&parse(DEFINITIONS.as_bytes()).unwrap());
    let Json::Obj(root) = &mut definitions else {
        panic!()
    };
    let Json::Arr(vs) = root.get_mut("vocabularies").unwrap() else {
        panic!()
    };
    let Json::Obj(v) = &mut vs[0] else { panic!() };
    let Json::Arr(ds) = v.get_mut("declarations").unwrap() else {
        panic!()
    };
    let Json::Obj(left) = &mut ds[0] else {
        panic!()
    };
    left.insert(
        "fields".into(),
        Json::Arr(vec![Json::obj([
            ("name", Json::str("root_qty")),
            ("type", Json::str("Z")),
            ("meaning", Json::str("root quantity")),
        ])]),
    );
    let definitions = definitions.canonical();
    let checked = check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Flow"].digest;
    let original = check_definitions(&[("definition0", DEFINITIONS.as_bytes())]).unwrap();
    let old = &original.vocabularies["Flow"].digest;
    let law = std::str::from_utf8(normal.law().bytes())
        .unwrap()
        .replace(old, digest);
    let mut map = super::fixture::convert(&parse(normal.archmap().bytes()).unwrap());
    let Json::Obj(root) = &mut map else { panic!() };
    let Json::Arr(snaps) = root.get_mut("snapshots").unwrap() else {
        panic!()
    };
    let Json::Obj(snap) = &mut snaps[0] else {
        panic!()
    };
    let Json::Arr(atoms) = snap.get_mut("atoms").unwrap() else {
        panic!()
    };
    atoms.push(Json::obj([
        ("id", Json::str("A-root_qty")),
        ("subject", Json::str("A")),
        ("field", Json::str("Flow.Left.root_qty")),
        ("value", Json::str("3")),
        ("origin", Json::str("o")),
    ]));
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.canonical().replace(old, digest).into_bytes(),
    )
}
