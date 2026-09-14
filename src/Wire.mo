/// Experimental internal delivery ABI. See the paired runtime wire.rs.
/// Only the transport envelope changes; each actor's argument/reply Blob stays
/// opaque. Parsing completes before invoking a private actor or continuation.
import Array "mo:core/Array";
import Blob "mo:core/Blob";
import Nat8 "mo:core/Nat8";
import Nat64 "mo:core/Nat64";
import Principal "mo:core/Principal";
import Runtime "mo:core/Runtime";
import Text "mo:core/Text";
import VarArray "mo:core/VarArray";
import Kernel "Kernel";

module {
  let maximum : Nat = 1_048_576;
  let magic : Blob = "MLA\01";

  func require(ok : Bool) { if (not ok) Runtime.trap("invalid packed local message") };
  class Reader(input : Blob) {
    require(input.size() <= maximum);
    let iter = input.values();
    var left = input.size();
    public func byte() : Nat8 {
      require(left > 0);
      left -= 1;
      switch (iter.next()) { case (?b) b; case null Runtime.trap("truncated packed local message") };
    };
    public func raw(size : Nat) : Blob {
      require(size <= left);
      Blob.fromArray(Array.tabulate<Nat8>(size, func _ { byte() }));
    };
    public func word(width : Nat) : Nat {
      require(width <= left);
      var n = 0; var scale = 1; var i = 0;
      while (i < width) { n += Nat8.toNat(byte()) * scale; scale *= 256; i += 1 };
      n;
    };
    public func blob(limit : Nat) : Blob {
      let size = word(4); require(size <= limit); raw(size);
    };
    public func text(limit : Nat) : Text {
      switch (Text.decodeUtf8(blob(limit))) {
        case (?value) value; case null Runtime.trap("invalid packed UTF-8");
      };
    };
    public func principal() : Principal {
      let size = Nat8.toNat(byte()); require(size <= 29);
      Principal.fromBlob(raw(size));
    };
    public func reference() : Kernel.Ref {
      let container = principal(); let slot = Nat64.fromNat(word(8)); let generation = Nat64.fromNat(word(8));
      { container; slot; generation };
    };
    public func continuation() : Kernel.Continuation {
      let owner = reference(); let slot = Nat64.fromNat(word(8)); let generation = Nat64.fromNat(word(8));
      { owner; slot; generation };
    };
    public func reply() : Kernel.Reply {
      switch (byte()) {
        case 0 #ok(blob(maximum)); case 1 #err(text(maximum));
        case _ Runtime.trap("invalid packed reply tag");
      };
    };
    public func end() { require(left == 0) };
  };

  func refSize(id : Kernel.Ref) : Nat { 17 + Principal.toBlob(id.container).size() };
  func contSize(id : Kernel.Continuation) : Nat { 16 + refSize(id.owner) };
  func textSize(text : Text) : Nat { 4 + Text.encodeUtf8(text).size() };
  func replySize(reply : Kernel.Reply) : Nat {
    switch reply { case (#ok bytes) 5 + bytes.size(); case (#err text) 1 + textSize(text) };
  };
  class Writer(size : Nat, kind : Nat8) {
    require(size <= maximum);
    let bytes = VarArray.repeat<Nat8>(0, size);
    var at = 0;
    public func byte(value : Nat8) { require(at < size); bytes[at] := value; at += 1 };
    public func raw(value : Blob) { for (b in value.values()) byte(b) };
    public func word(value : Nat, width : Nat) {
      var n = value; var i = 0;
      while (i < width) { byte(Nat8.fromNat(n % 256)); n /= 256; i += 1 };
      require(n == 0);
    };
    public func blob(value : Blob) { word(value.size(), 4); raw(value) };
    public func text(value : Text) { blob(Text.encodeUtf8(value)) };
    public func principal(value : Principal) {
      let bytes = Principal.toBlob(value); require(bytes.size() <= 29);
      byte(Nat8.fromNat(bytes.size())); raw(bytes);
    };
    public func reference(id : Kernel.Ref) {
      principal(id.container); word(Nat64.toNat(id.slot), 8); word(Nat64.toNat(id.generation), 8);
    };
    public func continuation(id : Kernel.Continuation) {
      reference(id.owner); word(Nat64.toNat(id.slot), 8); word(Nat64.toNat(id.generation), 8);
    };
    public func reply(value : Kernel.Reply) {
      switch value { case (#ok value) { byte(0); blob(value) }; case (#err value) { byte(1); text(value) } };
    };
    public func finish() : Blob { require(at == size); Blob.fromVarArray(bytes) };
    raw(magic); byte(kind);
  };

  func frame(value : Kernel.Frame) : Blob {
    require(value.retired.size() <= 128);
    var size = 9; // Magic, frame kind, retirement count.
    for (id in value.retired.values()) size += refSize(id);
    size += switch (value.outcome) {
      case (#done reply) replySize(reply);
      case (#readOnly _) Runtime.trap("query results require authenticated transport");
      case (#suspended action) {
        let targetSize = switch (action.request) {
          case (#local call) {
            require(Text.encodeUtf8(call.method).size() <= 128);
            refSize(call.target) + textSize(call.method) + 4 + call.arg.size();
          };
          case (#rooted _) Runtime.trap("scalar roots require authenticated transport");
          case (#external call) {
            require(Text.encodeUtf8(call.method).size() <= 128);
            1 + Principal.toBlob(call.target).size() + textSize(call.method) + 4 + call.arg.size();
          };
        };
        1 + contSize(action.continuation) + targetSize;
      };
    };
    let w = Writer(size, 3);
    switch (value.outcome) {
      case (#done reply) w.reply(reply);
      case (#readOnly _) Runtime.trap("query results require authenticated transport");
      case (#suspended action) {
        switch (action.request) {
          case (#local call) {
            w.byte(2); w.continuation(action.continuation); w.reference(call.target); w.text(call.method); w.blob(call.arg);
          };
          case (#rooted _) Runtime.trap("scalar roots require authenticated transport");
          case (#external call) {
            w.byte(3); w.continuation(action.continuation); w.principal(call.target); w.text(call.method); w.blob(call.arg);
          };
        };
      };
    };
    w.word(value.retired.size(), 4);
    for (id in value.retired.values()) w.reference(id);
    w.finish();
  };

  public func handle(kernel : Kernel.Kernel, input : Blob) : Blob {
    let r = Reader(input);
    require(r.raw(4) == magic);
    switch (r.byte()) {
      case 0 {
        let id = r.reference(); let method = r.text(128); let arg = r.blob(maximum);
        r.end(); frame(kernel.dispatch(id, method, arg));
      };
      case 1 {
        let id = r.continuation(); let reply = r.reply();
        r.end(); frame(kernel.resume(id, reply));
      };
      case 2 {
        let id = r.continuation(); r.end();
        let canceled = kernel.cancel(id);
        let w = Writer(6, 4); w.byte(if canceled 1 else 0); w.finish();
      };
      case _ Runtime.trap("invalid packed operation tag");
    };
  };
};
