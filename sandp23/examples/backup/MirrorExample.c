/* JSON Value API */
_Mirror JSON_Value_Type json_value_get_type  
      (_TPtr<const TJSON_Value> value) {
    return value ? value->type : JSONError;
}