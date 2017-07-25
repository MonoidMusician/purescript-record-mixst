"use strict";

exports.rawCopy = function(r) {
  return function() {
    var copy = {};
    for (var key in rec) {
      if ({}.hasOwnProperty.call(rec, key)) {
        copy[key] = rec[key];
      }
    }
    return copy;
  };
};

exports.rawExists = function(k) {
  return function(r) {
    return function() {
      return {}.hasOwnProperty.call(r, k);
    };
  };
};

exports.rawGet = function(k) {
  return function(r) {
    return function() {
      return r[k];
    };
  };
};

exports.rawSet = function(k) {
  return function(v) {
    return function(r) {
      return function() {
        r[k] = v;
      };
    };
  };
};

exports.rawDelete = function(k) {
  return function(r) {
    return function() {
      delete r[k];
    };
  };
};
