"use strict";

exports.rawCopy = function(r) {
  return function() {
    var copy = {};
    for (var key in r) {
      if ({}.hasOwnProperty.call(r, key)) {
        copy[key] = r[key];
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
