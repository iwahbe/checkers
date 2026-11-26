module ctor_home.kinds

export enum Inner
    A
    B

export enum Outer
    Wrap i : i~Inner
    Empty

export fn wrapped -> o : o~Outer
    Wrap B
