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
});
