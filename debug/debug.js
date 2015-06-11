$(function () {
    $("button.shrink").on("click", function (e) {
        trace = $(this).parent().parent();
        $(trace).find("div.verifyRefineLoop").toggle();
        $(trace).find("div.candidate").toggle();
        if ($(this).html() == "-") {
            $(this).html("+");
        } else {
            $(this).html("-");
        }
    });

    /* Populate options */
    var varnames = $("#optionsVarnames").text().split(", ");
    varnames.forEach(function (v) {
        $("#optionsDialog").append($("<br />"));
        $("#optionsDialog").append(
            $("<input />", {
                type: "checkbox",
                'class': "varCheckBox",
                'checked': "checked",
                name: v,
                id: 'cb'+v
            })
        );
        $("#optionsDialog").append(
            $("<label />", {
                'for': 'cb'+v,
                text: v
            })
        );
    });

    $(".varCheckBox").change(function () {
        var v = $(this).attr('name');
        if ($(this).is(":checked")) {
            $(".var_" + v).show();
        } else {
            $(".var_" + v).hide();
        }
    });

    $("#optionsDialog").dialog({
        autoOpen: false
    });

    $("#options").on("click", function (e) {
        $("#optionsDialog").dialog("open");
    });

});
