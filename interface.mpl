# Copyright (C) 2021 Matway Burkow
#
# This repository and all its contents belong to Matway Burkow (referred here and below as "the owner").
# The content is for demonstration purposes only.
# It is forbidden to use the content or any part of it for any purpose without explicit permission from the owner.
# By contributing to the repository, contributors acknowledge that ownership of their work transfers to the owner.

"algorithm.each" use
"algorithm.findOrdinal" use
"control.Natx" use
"control.Ref" use
"control.assert" use
"control.bind" use
"control.drop" use
"control.dup" use
"control.isBuiltinTuple" use
"control.isVirtual" use
"control.pfunc" use
"control.times" use
"control.unwrap" use
"control.when" use
"control.while" use

fieldIsRef: [drop drop FALSE];
fieldIsRef: [index: object:;; index @object @ Ref index @object ! TRUE] [drop drop TRUE] pfunc;
fieldIsref: [isConst] [0 .ERROR_CAN_ONLY_HANDLE_MUTABLE_OBJECTS] pfunc;

cloneField: [
  index: object:;;
  index @object @ index @object fieldIsRef [Ref] [newVarOfTheSameType] if
];

interface: [
  virtual methods: call dup isVirtual ~ [Ref] when;
  index: 0;
  inputIndex: 0;

  fillInputs: [
    inputIndex index @methods @ fieldCount 1 - = [] [
      inputIndex index @methods @ cloneField index @methods @ inputIndex fieldName def
      inputIndex 1 + !inputIndex
      @fillInputs ucall
    ] uif
  ];

  fillVtable: [
    index @methods fieldCount = [] [
      {
        self: Natx;
        0 !inputIndex
        @fillInputs ucall
      }

      index @methods @ fieldCount 1 - index @methods @ cloneField
      {} codeRef
      @methods index fieldName def
      index 1 + !index
      @fillVtable ucall
    ] uif
  ];

  {
    Vtable: {
      DIE_FUNC: {self: Natx;} {} {} codeRef;
      [drop] !DIE_FUNC
      SIZE: {self: Natx;} Natx {} codeRef;
      ADDRESS_OFFSET: Natx;
      @fillVtable ucall
    };

    CALL: [
      fillMethods: [
        index @Vtable fieldCount = [] [
          @Vtable index fieldName "CALL" = [
            [@closure storageAddress vtable.ADDRESS_OFFSET - @vtable.CALL]
          ] [
            {
              virtual NAME: @Vtable index fieldName;
              CALL: [@self storageAddress vtable.ADDRESS_OFFSET - @vtable NAME callField];
            }
          ] if

          @Vtable index fieldName def
          index 1 + !index
          @fillMethods ucall
        ] uif
      ];

      index: 1;

      {
        vtable: @Vtable;
        DIE: [@closure storageAddress vtable.ADDRESS_OFFSET - @vtable.DIE_FUNC];
        @fillMethods ucall
      }
    ];
  }
];

implement: [
  interfacesToImplement: getObject:;;

  {
    virtual interfaces: ((interfacesToImplement) [Ref] each);
    virtual getObject: @getObject;
    vtables: (interfaces [.@vtable newVarOfTheSameType] each);

    createBases: [
      (@vtables [{vtable:;}] each)
    ];

    CALL: [
      moveFields: [
        index @object fieldCount = [] [
          index @object @ index @object fieldIsRef ~ [new] when @object index fieldName def
          index 1 + !index
          @moveFields ucall
        ] uif
      ];

      object: getObject;
      index: 0;

      {
        virtual interfaces: @interfaces;

        bases: createBases;

        [
          size: 0nx;
          @bases [
            base:;
            size new @base.@vtable.!ADDRESS_OFFSET
            size base storageSize + !size
          ] each
        ] call

        castToBase: [
          baseType: Ref;
          @interfaces [baseType same] findOrdinal index:;
          index -1 = ["fail" raiseStaticError] when
          base: index @bases @;
          base storageAddress index @interfaces @ addressToReference
        ];

        @moveFields ucall
      }
    ];

    [
      virtual Object: CALL Ref;
      @vtables [
        vtable:;
        [@Object addressToReference manuallyDestroyVariable] @vtable.!DIE_FUNC
        [drop @Object storageSize] @vtable.!SIZE
        i: 3; [i @vtable fieldCount = ~] [
          virtual NAME: @vtable i fieldName;
          [@Object addressToReference NAME callField] i @vtable !
          i 1 + !i
        ] while
      ] each
    ] call
  }
];
